//! Plexi: a small source-to-source translator from Restricted Algorithmic
//! Rust (RAR) to Restricted Algorithmic C (RAC).
//!
//! Usage:  plexi INPUT.rs OUTPUT.cpp [-D NAME=VALUE]...
//!
//! Only the text between the comments `// RAR begin` and `// RAR end` is
//! translated.  The `-D NAME=VALUE` option overrides the value of a global
//! `const` (used to build instances with different array sizes).
//!
//! Supported RAR subset:
//!   items:      #[attr] (ignored), const, struct, fn
//!   types:      bool, u8..u64, usize, i8..i64, isize, [T; N]
//!   statements: let [mut] x: T [= e];  if/else if/else;  return e;
//!               expression statements (assignments, calls);
//!               cfor!(let mut i: T = e; test; update; { body });
//!   expressions are copied token by token (Rust and C agree on the
//!   operators used by RAR: field access, indexing, calls, arithmetic,
//!   comparison, logical and bitwise operators).

use std::collections::HashMap;
use std::fmt::Write as _;
use std::process::exit;

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Ident(String),
    Num(String),
    Punct(String),
}

impl Tok {
    fn text(&self) -> &str {
        match self {
            Tok::Ident(s) | Tok::Num(s) | Tok::Punct(s) => s,
        }
    }
}

#[derive(Clone, Debug)]
struct Token {
    tok: Tok,
    line: usize,
}

fn die(msg: &str) -> ! {
    eprintln!("plexi: error: {}", msg);
    exit(1)
}

fn lex(src: &str, first_line: usize) -> Vec<Token> {
    let cs: Vec<char> = src.chars().collect();
    let mut i = 0;
    let mut line = first_line;
    let mut out = Vec::new();
    const PUNCT3: [&str; 3] = ["<<=", ">>=", "..="];
    const PUNCT2: [&str; 20] = [
        "==", "!=", "<=", ">=", "&&", "||", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=",
        "<<", ">>", "->", "::", "..", "=>",
    ];
    while i < cs.len() {
        let c = cs[i];
        if c == '\n' {
            line += 1;
            i += 1;
        } else if c.is_whitespace() {
            i += 1;
        } else if c == '/' && i + 1 < cs.len() && cs[i + 1] == '/' {
            while i < cs.len() && cs[i] != '\n' {
                i += 1;
            }
        } else if c == '/' && i + 1 < cs.len() && cs[i + 1] == '*' {
            i += 2;
            while i + 1 < cs.len() && !(cs[i] == '*' && cs[i + 1] == '/') {
                if cs[i] == '\n' {
                    line += 1;
                }
                i += 1;
            }
            i += 2;
        } else if c.is_alphabetic() || c == '_' {
            let s = i;
            while i < cs.len() && (cs[i].is_alphanumeric() || cs[i] == '_') {
                i += 1;
            }
            out.push(Token { tok: Tok::Ident(cs[s..i].iter().collect()), line });
        } else if c.is_ascii_digit() {
            let s = i;
            while i < cs.len() && (cs[i].is_ascii_alphanumeric() || cs[i] == '_') {
                i += 1;
            }
            let raw: String = cs[s..i].iter().filter(|c| **c != '_').collect();
            // Strip Rust integer suffixes (e.g. 1usize, 7i64).
            let mut num = raw.clone();
            for suf in ["usize", "isize", "u64", "u32", "u16", "u8", "i64", "i32", "i16", "i8"] {
                if num.ends_with(suf) && num.len() > suf.len() && !num.starts_with("0x") {
                    num.truncate(num.len() - suf.len());
                    break;
                }
            }
            out.push(Token { tok: Tok::Num(num), line });
        } else {
            let rest: String = cs[i..std::cmp::min(i + 3, cs.len())].iter().collect();
            let p = PUNCT3
                .iter()
                .find(|p| rest.starts_with(**p))
                .or_else(|| PUNCT2.iter().find(|p| rest.starts_with(**p)))
                .map(|p| p.to_string())
                .unwrap_or_else(|| c.to_string());
            i += p.chars().count();
            out.push(Token { tok: Tok::Punct(p), line });
        }
    }
    out
}

struct Parser {
    toks: Vec<Token>,
    pos: usize,
    consts: HashMap<String, String>,
    overrides: HashMap<String, String>,
    out: String,
}

/// Map a scalar RAR type to its RAC name.
fn scalar_type(name: &str) -> Option<&'static str> {
    Some(match name {
        "bool" => "bool",
        "u8" => "u8",
        "u16" => "u16",
        "u32" => "u32",
        "u64" => "u64",
        "usize" => "usize",
        "i8" => "i8",
        "i16" => "i16",
        "i32" => "i32",
        "i64" => "i64",
        "isize" => "isize",
        _ => return None,
    })
}

const TYPEDEFS: &str = "\
typedef ac_int<8, false> u8;
typedef ac_int<16, false> u16;
typedef ac_int<32, false> u32;
typedef ac_int<64, false> u64;
typedef ac_int<64, false> usize;
typedef ac_int<8, true> i8;
typedef ac_int<16, true> i16;
typedef ac_int<32, true> i32;
typedef ac_int<64, true> i64;
typedef ac_int<64, true> isize;
";

impl Parser {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|t| &t.tok)
    }
    fn peek_text(&self) -> &str {
        self.peek().map(|t| t.text()).unwrap_or("")
    }
    fn peek_at(&self, k: usize) -> &str {
        self.toks.get(self.pos + k).map(|t| t.tok.text()).unwrap_or("")
    }
    fn line(&self) -> usize {
        self.toks
            .get(self.pos)
            .or(self.toks.last())
            .map(|t| t.line)
            .unwrap_or(0)
    }
    fn err(&self, msg: &str) -> ! {
        die(&format!("line {}: {} (at `{}`)", self.line(), msg, self.peek_text()))
    }
    fn next(&mut self) -> Tok {
        match self.toks.get(self.pos) {
            Some(t) => {
                self.pos += 1;
                t.tok.clone()
            }
            None => self.err("unexpected end of input"),
        }
    }
    fn expect(&mut self, s: &str) {
        if self.peek_text() != s {
            self.err(&format!("expected `{}`", s));
        }
        self.pos += 1;
    }
    fn eat(&mut self, s: &str) -> bool {
        if self.peek_text() == s {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn ident(&mut self) -> String {
        match self.next() {
            Tok::Ident(s) => s,
            _ => {
                self.pos -= 1;
                self.err("expected identifier")
            }
        }
    }

    /// Parse a type; returns (element type, optional array dimension).
    fn parse_type(&mut self) -> (String, Option<String>) {
        if self.eat("[") {
            let (elt, dim) = self.parse_type();
            if dim.is_some() {
                self.err("nested arrays are not supported");
            }
            self.expect(";");
            let n = self.expr_until(&["]"]);
            self.expect("]");
            (elt, Some(n))
        } else {
            let name = self.ident();
            match scalar_type(&name) {
                Some(t) => (t.to_string(), None),
                None => (name, None), // a struct type
            }
        }
    }

    fn type_str(&self, ty: &(String, Option<String>)) -> String {
        match &ty.1 {
            None => ty.0.clone(),
            Some(n) => format!("array<{}, {}>", ty.0, n),
        }
    }

    /// Collect the tokens of an expression up to (not including) one of the
    /// given terminators at bracket depth 0, and render them as C.
    fn expr_until(&mut self, stops: &[&str]) -> String {
        let mut depth: i32 = 0;
        let mut parts: Vec<String> = Vec::new();
        loop {
            let t = match self.peek() {
                Some(t) => t.clone(),
                None => self.err("unterminated expression"),
            };
            let s = t.text().to_string();
            if depth == 0 && stops.contains(&s.as_str()) {
                break;
            }
            match s.as_str() {
                "(" | "[" | "{" => depth += 1,
                ")" | "]" | "}" => {
                    depth -= 1;
                    if depth < 0 {
                        self.err("unbalanced brackets in expression");
                    }
                }
                "as" => self.err("`as` casts are not supported by this RAR translator"),
                _ => {}
            }
            self.pos += 1;
            parts.push(s);
        }
        if parts.is_empty() {
            self.err("empty expression");
        }
        render_expr(&parts)
    }

    fn emit(&mut self, indent: usize, s: &str) {
        for _ in 0..indent {
            self.out.push_str("  ");
        }
        self.out.push_str(s);
        self.out.push('\n');
    }

    fn parse_items(&mut self) {
        while self.pos < self.toks.len() {
            match self.peek_text() {
                "#" => self.skip_attr(),
                "const" => self.parse_const(),
                "struct" => self.parse_struct(),
                "fn" => self.parse_fn(),
                _ => self.err("expected an item (const, struct or fn)"),
            }
        }
    }

    fn skip_attr(&mut self) {
        self.expect("#");
        self.eat("!");
        self.expect("[");
        let mut depth = 1;
        while depth > 0 {
            match self.next().text() {
                "[" => depth += 1,
                "]" => depth -= 1,
                _ => {}
            }
        }
    }

    fn parse_const(&mut self) {
        self.expect("const");
        let name = self.ident();
        self.expect(":");
        let ty = self.parse_type();
        if ty.1.is_some() {
            self.err("array constants are not supported");
        }
        self.expect("=");
        let mut val = self.expr_until(&[";"]);
        self.expect(";");
        if let Some(v) = self.overrides.get(&name) {
            val = v.clone();
        }
        self.consts.insert(name.clone(), val.clone());
        // Global integer constants become RAC `uint`/`int` constants, so that
        // they may be used as array dimensions.
        let cty = match ty.0.as_str() {
            "usize" | "u8" | "u16" | "u32" | "u64" => "uint",
            "bool" => "bool",
            _ => "int",
        };
        self.emit(0, &format!("const {} {} = {};", cty, name, val));
        self.out.push('\n');
    }

    fn parse_struct(&mut self) {
        self.expect("struct");
        let name = self.ident();
        self.expect("{");
        self.emit(0, &format!("struct {} {{", name));
        while !self.eat("}") {
            let f = self.ident();
            self.expect(":");
            let ty = self.parse_type();
            let ts = self.type_str(&ty);
            self.emit(1, &format!("{} {};", ts, f));
            if !self.eat(",") {
                self.expect("}");
                break;
            }
        }
        self.emit(0, "};");
        self.out.push('\n');
    }

    fn parse_fn(&mut self) {
        self.expect("fn");
        let name = self.ident();
        self.expect("(");
        let mut params = Vec::new();
        while !self.eat(")") {
            self.eat("mut");
            let p = self.ident();
            self.expect(":");
            let ty = self.parse_type();
            params.push(format!("{} {}", self.type_str(&ty), p));
            if !self.eat(",") {
                self.expect(")");
                break;
            }
        }
        let ret = if self.eat("->") {
            let ty = self.parse_type();
            self.type_str(&ty)
        } else {
            "void".to_string()
        };
        self.out
            .push_str(&format!("{} {}({}) ", ret, name, params.join(", ")));
        self.parse_block(0);
        self.out.push('\n');
    }

    /// Parse `{ stmts }`; the opening brace is written at the current
    /// position of the output, the body at indent+1.
    fn parse_block(&mut self, indent: usize) {
        self.expect("{");
        self.out.push_str("{\n");
        while !self.eat("}") {
            self.parse_stmt(indent + 1);
        }
        for _ in 0..indent {
            self.out.push_str("  ");
        }
        self.out.push_str("}\n");
    }

    /// `let [mut] x: T [= e]` without the terminating `;`.
    fn parse_let(&mut self) -> String {
        self.expect("let");
        self.eat("mut");
        let v = self.ident();
        if self.peek_text() != ":" {
            self.err("RAR requires an explicit type on every `let`");
        }
        self.expect(":");
        let ty = self.parse_type();
        let ts = self.type_str(&ty);
        if self.eat("=") {
            let e = self.expr_until(&[";"]);
            format!("{} {} = {}", ts, v, e)
        } else if ty.1.is_some() {
            format!("{} {}", ts, v)
        } else {
            // RAC requires every scalar variable to be initialized.
            format!("{} {} = 0", ts, v)
        }
    }

    fn parse_if(&mut self, indent: usize) {
        self.expect("if");
        let c = self.expr_until(&["{"]);
        self.out.push_str(&format!("if ({}) ", strip_parens(&c)));
        self.parse_block(indent);
        if self.eat("else") {
            // replace the trailing "}\n" with "} else "
            self.out.pop();
            self.out.push_str(" else ");
            if self.peek_text() == "if" {
                self.parse_if(indent);
            } else {
                self.parse_block(indent);
            }
        }
    }

    fn parse_stmt(&mut self, indent: usize) {
        let pad = "  ".repeat(indent);
        match self.peek_text() {
            "let" => {
                let s = self.parse_let();
                self.expect(";");
                self.emit(indent, &format!("{};", s));
            }
            "if" => {
                self.out.push_str(&pad);
                self.parse_if(indent);
            }
            "return" => {
                self.expect("return");
                let e = self.expr_until(&[";"]);
                self.expect(";");
                self.emit(indent, &format!("return {};", e));
            }
            "{" => {
                self.out.push_str(&pad);
                self.parse_block(indent);
            }
            "cfor" if self.peek_at(1) == "!" => {
                self.expect("cfor");
                self.expect("!");
                self.expect("(");
                let init = if self.peek_text() == "let" {
                    // RAC loop counters are native integers, so that the
                    // generated recursive function has a simple measure.
                    let l = self.parse_let();
                    loop_counter(&l)
                } else {
                    self.expr_until(&[";"])
                };
                self.expect(";");
                let test = self.expr_until(&[";"]);
                self.expect(";");
                let update = self.expr_until(&[";"]);
                self.expect(";");
                self.out.push_str(&format!(
                    "{}for ({}; {}; {}) ",
                    pad,
                    init,
                    strip_parens(&test),
                    update
                ));
                self.parse_block(indent);
                self.expect(")");
                self.eat(";");
            }
            ";" => {
                self.pos += 1;
            }
            _ => {
                let e = self.expr_until(&[";"]);
                self.expect(";");
                self.emit(indent, &format!("{};", e));
            }
        }
    }
}

/// Retype the declaration of a loop counter: unsigned -> uint, signed -> int.
fn loop_counter(decl: &str) -> String {
    let (ty, rest) = decl.split_once(' ').unwrap_or((decl, ""));
    let nty = match ty {
        "usize" | "u8" | "u16" | "u32" | "u64" => "uint",
        "isize" | "i8" | "i16" | "i32" | "i64" => "int",
        _ => die(&format!("unsupported loop counter type `{}`", ty)),
    };
    format!("{} {}", nty, rest)
}

/// Render expression tokens as C text, with conventional spacing.
fn render_expr(parts: &[String]) -> String {
    let mut s = String::new();
    let binops = [
        "==", "!=", "<=", ">=", "&&", "||", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<",
        ">>", "<<=", ">>=", "=", "<", ">", "+", "*", "/", "%", "&", "|", "^", "-",
    ];
    let mut prev: Option<&str> = None;
    for p in parts {
        let p = p.as_str();
        let is_bin = binops.contains(&p);
        // A '-' is unary if it follows nothing, an operator or an open bracket.
        let unary_minus = p == "-"
            && match prev {
                None => true,
                Some(q) => binops.contains(&q) || q == "(" || q == "[" || q == "," || q == "!",
            };
        if is_bin && !unary_minus {
            let _ = write!(s, " {} ", p);
        } else if p == "," {
            s.push_str(", ");
        } else {
            s.push_str(p);
        }
        prev = Some(p);
    }
    s
}

/// Remove one pair of redundant outer parentheses, e.g. `(a < b)` -> `a < b`.
fn strip_parens(s: &str) -> String {
    let t = s.trim();
    if t.starts_with('(') && t.ends_with(')') {
        let inner = &t[1..t.len() - 1];
        let mut depth = 0i32;
        for c in inner.chars() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth < 0 {
                        return t.to_string();
                    }
                }
                _ => {}
            }
        }
        if depth == 0 {
            return inner.to_string();
        }
    }
    t.to_string()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut files = Vec::new();
    let mut overrides = HashMap::new();
    let mut i = 1;
    while i < args.len() {
        if args[i] == "-D" {
            let d = args.get(i + 1).unwrap_or_else(|| die("-D needs NAME=VALUE"));
            let (n, v) = d.split_once('=').unwrap_or_else(|| die("-D needs NAME=VALUE"));
            overrides.insert(n.to_string(), v.to_string());
            i += 2;
        } else {
            files.push(args[i].clone());
            i += 1;
        }
    }
    if files.len() != 2 {
        die("usage: plexi INPUT.rs OUTPUT.cpp [-D NAME=VALUE]...");
    }
    let src = std::fs::read_to_string(&files[0])
        .unwrap_or_else(|e| die(&format!("cannot read {}: {}", files[0], e)));
    let begin = src
        .find("// RAR begin")
        .unwrap_or_else(|| die("missing `// RAR begin`"));
    let body_start = begin + src[begin..].find('\n').unwrap_or(0);
    let end = src[body_start..]
        .find("// RAR end")
        .map(|e| e + body_start)
        .unwrap_or_else(|| die("missing `// RAR end`"));
    let first_line = src[..body_start].matches('\n').count() + 1;
    let toks = lex(&src[body_start..end], first_line);

    let mut p = Parser { toks, pos: 0, consts: HashMap::new(), overrides, out: String::new() };
    p.parse_items();
    for k in p.overrides.keys() {
        if !p.consts.contains_key(k) {
            die(&format!("-D {}: no such constant", k));
        }
    }

    let mut out = String::new();
    out.push_str(&format!(
        "// Generated by plexi from {} -- do not edit.\n\n",
        files[0]
    ));
    out.push_str("#include <ac_int.h>\n#include <rac.h>\n#include <array>\nusing namespace std;\n\n");
    out.push_str("// RAC begin\n\n");
    out.push_str(TYPEDEFS);
    out.push('\n');
    out.push_str(&p.out);
    out.push_str("// RAC end\n");
    std::fs::write(&files[1], out)
        .unwrap_or_else(|e| die(&format!("cannot write {}: {}", files[1], e)));
}
