#!/usr/bin/env python3
"""Whitespace- and comment-insensitive, item-by-item audit of the adapted
subject (subject/src/lib.rs) against the pristine upstream file
(subject/fixslice32.upstream.rs, aes 0.9.1 src/soft/fixslice32.rs).

Each file is split into top-level items (functions, types, uses, macro
definitions and invocations, modules), each item keyed by its kind and name.
Comments are removed and whitespace is collapsed before comparison; attributes
(#[cfg], #[inline], ...) are kept, so a removed cfg gate counts as a
difference.  The output is a classified inventory:

  identical        items whose normalized text is the same
  changed          items present in both whose text differs (with a diff)
  removed          upstream items absent from the subject
  added            subject items absent from upstream

Usage: audit.py UPSTREAM SUBJECT  (exit status 0; prints the inventory)
"""
import difflib
import re
import sys


def strip_comments(src):
    out, i, n = [], 0, len(src)
    while i < n:
        if src.startswith('//', i):
            j = src.find('\n', i)
            i = n if j < 0 else j
        elif src.startswith('/*', i):
            j = src.find('*/', i + 2)
            i = n if j < 0 else j + 2
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            out.append(src[i:j + 1])
            i = j + 1
        else:
            out.append(src[i])
            i += 1
    return ''.join(out)


def split_items(src):
    """Top-level items: text up to a ';' or a balanced '{...}' at depth 0."""
    src = strip_comments(src)
    items, cur, depth, i = [], [], 0, 0
    while i < len(src):
        c = src[i]
        cur.append(c)
        if c == '"':
            j = i + 1
            while j < len(src) and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            cur.append(src[i + 1:j + 1])
            i = j + 1
            continue
        if c in '{([':
            depth += 1
        elif c in '})]':
            depth -= 1
            if depth == 0 and c == '}':
                text = ''.join(cur).strip()
                # a macro invocation or similar may continue with ';'
                k = i + 1
                while k < len(src) and src[k] in ' \t\n':
                    k += 1
                if k < len(src) and src[k] == ';':
                    text += ';'
                    i = k
                items.append(text)
                cur = []
        elif c == ';' and depth == 0:
            items.append(''.join(cur).strip())
            cur = []
        i += 1
    rest = ''.join(cur).strip()
    if rest:
        items.append(rest)
    return [t for t in items if t]


def normalize(text):
    return re.sub(r'\s+', ' ', text).strip()


def item_key(text):
    body = re.sub(r'^(\s*#!?\[[^\]]*\]\s*)*', '', text)
    m = re.match(r'(pub(\([^)]*\))?\s+)?(fn|type|const|static|struct|enum|mod|use|macro_rules!)\s*([A-Za-z0-9_:{}, *]+)', body)
    if m:
        return '%s %s' % (m.group(3), m.group(4).strip())
    m = re.match(r'([A-Za-z_][A-Za-z0-9_]*)!\s*\(\s*([A-Za-z0-9_]+)', body)
    if m:
        return '%s!(%s)' % (m.group(1), m.group(2))
    return 'item ' + normalize(body)[:40]


def items_by_key(src):
    d = {}
    order = []
    for t in split_items(src):
        k = item_key(t)
        while k in d:
            k += "'"
        d[k] = normalize(t)
        order.append(k)
    return d, order


def tokens(s):
    return re.findall(r'[A-Za-z0-9_]+|"[^"]*"|\S', s)


def main():
    up, up_order = items_by_key(open(sys.argv[1]).read())
    sub, sub_order = items_by_key(open(sys.argv[2]).read())
    identical = [k for k in up_order if k in sub and up[k] == sub[k]]
    changed = [k for k in up_order if k in sub and up[k] != sub[k]]
    removed = [k for k in up_order if k not in sub]
    added = [k for k in sub_order if k not in up]
    print('identical (%d): %s' % (len(identical), ', '.join(identical)))
    print()
    print('changed (%d):' % len(changed))
    for k in changed:
        print('  ' + k)
        a = ' '.join(tokens(up[k])).replace(' ; ', ' ;\n').replace(' { ', ' {\n').replace(' } ', ' }\n').split('\n')
        b = ' '.join(tokens(sub[k])).replace(' ; ', ' ;\n').replace(' { ', ' {\n').replace(' } ', ' }\n').split('\n')
        for line in difflib.unified_diff(a, b, 'upstream', 'subject', lineterm='', n=0):
            if line.startswith(('---', '+++', '@@')):
                continue
            print('      ' + line)
    print()
    print('removed (%d): %s' % (len(removed), ', '.join(removed)))
    print()
    print('added (%d): %s' % (len(added), ', '.join(added)))


if __name__ == '__main__':
    main()
