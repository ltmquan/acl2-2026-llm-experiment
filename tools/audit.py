#!/usr/bin/env python3
"""Deterministic internet/cheating audit of saved model-run transcripts.

Usage: python3 -I audit.py <transcripts-dir> [<task> ...] [--until=<task>@<ISO time> ...]

<transcripts-dir>/<task>/page-*.txt are raw list_events pages (kinds: assistant and result),
saved verbatim. Each page contains one JSON object {"ccr": {...}} (possibly inside an
<other-session> wrapper). The script:
  1. extracts every tool call (id, time, tool name, input) from assistant events, de-duplicated by id;
  2. extracts per-turn server-side tool counters (web_search_requests, web_fetch_requests) from result events;
  3. flags
     - any tool not in the allowlist (Bash, Read, Write, Edit, Glob, Grep, NotebookEdit, TaskStop, Agent),
     - any Bash command (or other tool input) matching network/package patterns,
     - any nonzero server-side web counters;
  4. checks completeness: the oldest page must have has_more == false.
Output: one line per task (CLEAN / FLAGGED / INCOMPLETE) plus details, and <dir>/<task>/audit.json.
"""
import json, re, sys, glob, os

ALLOWED = {"Bash", "Read", "Write", "Edit", "Glob", "Grep", "NotebookEdit", "TaskStop", "Agent",
           "Monitor", "SendUserFile", "TaskCreate", "TaskUpdate", "TaskGet", "TaskList"}  # all local, no network
NET = re.compile(
    r"\b(curl|wget|pip3?|pipx|apt(-get)?|npm|npx|yarn|gem|cargo|go\s+get|conda|uv\s+pip|"
    r"git\s+(clone|fetch|pull|ls-remote|remote|submodule)|ssh|scp|telnet|ftp|"
    r"urllib|requests\.|http\.client|socket\.|aiohttp|httpx)\b"
    r"|https?://|github|gitlab|arxiv|pypi|raw\.githubusercontent", re.I)
NC = re.compile(r"(^|[\s;&|(])nc\s+(-\w+\s+)*[\w.-]+\s+\d+")   # netcat invocation, case-sensitive

def load_pages(d):
    pages = []
    for f in sorted(glob.glob(os.path.join(d, "page-*.txt"))):
        s = open(f, encoding="utf-8").read()
        i = s.find('{"ccr"')
        if i < 0:
            raise SystemExit(f"{f}: no ccr JSON found")
        obj, _ = json.JSONDecoder().raw_decode(s[i:])
        pages.append((f, obj["ccr"]))
    return pages

def audit(d):
    pages = load_pages(d)
    # pages are saved newest-first; the service omits has_more on the oldest page
    complete = bool(pages) and not pages[-1][1].get("has_more", False)
    calls, counters = {}, []
    for _, p in pages:
        for ev in p.get("data", []):
            if "assistant" in ev:
                msg = ev["assistant"].get("internal_anthropic_catchall", {}).get("message", {})
                for c in msg.get("content", []) or []:
                    if c.get("type") == "tool_use":
                        calls[c["id"]] = {"t": ev.get("created_at"), "name": c.get("name"),
                                          "input": c.get("input")}
            if "result" in ev:
                r = ev["result"].get("internal_anthropic_catchall", {})
                stu = (r.get("usage") or {}).get("server_tool_use") or {}
                ws = sum((m or {}).get("webSearchRequests", 0) for m in (r.get("modelUsage") or {}).values())
                counters.append({"t": ev.get("created_at"),
                                 "web_search": stu.get("web_search_requests", 0) + ws,
                                 "web_fetch": stu.get("web_fetch_requests", 0)})
    # the run is the whole transcript, unless a cut-off is given (e.g. when someone messaged the session
    # after the run); then everything after the cut-off is reported as post-run
    run_end = UNTIL.get(os.path.basename(d.rstrip("/"))) or max((k["t"] for k in counters if k["t"]), default=None)
    flags, post = [], []
    for cid, c in sorted(calls.items(), key=lambda kv: kv[1]["t"] or ""):
        if run_end and c["t"] and c["t"] > run_end:
            post.append({"name": c["name"], "t": c["t"]})
            continue
        txt = json.dumps(c["input"], ensure_ascii=False)
        if c["name"] not in ALLOWED:
            flags.append({"why": "tool not allowed", **c})
        elif NET.search(txt) or NC.search(txt):
            # local file paths that merely contain the word 'github' etc. are still reported; human decides
            m = NET.search(txt) or NC.search(txt)
            flags.append({"why": "network-like pattern", "match": m.group(0).strip(), **c})
    for k in [k for k in counters if not run_end or (k["t"] or "") <= run_end]:
        if k["web_search"] or k["web_fetch"]:
            flags.append({"why": "server-side web tool use", **k})
    run_calls = len(calls) - len(post)
    return {"pages": len(pages), "complete": complete, "run_end": run_end, "tool_calls": run_calls,
            "post_run_calls": post,
            "tools": sorted({c["name"] for c in calls.values() if not (run_end and c["t"] and c["t"] > run_end)}),
            "result_events": len(counters),
            "flags": flags}

UNTIL = {}

def main():
    args = sys.argv[1:]
    for a in [a for a in args if a.startswith("--until=")]:
        task, ts = a[len("--until="):].split("@", 1); UNTIL[task] = ts; args.remove(a)
    root = args[0]
    tasks = args[1:] or sorted(os.listdir(root))
    for t in tasks:
        d = os.path.join(root, t)
        if not os.path.isdir(d):
            continue
        a = audit(d)
        json.dump(a, open(os.path.join(d, "audit.json"), "w"), indent=1, ensure_ascii=False)
        status = "INCOMPLETE" if not a["complete"] else ("FLAGGED" if a["flags"] else "CLEAN")
        print(f"{t}: {status}  pages={a['pages']} run_tool_calls={a['tool_calls']} run_end={a['run_end']} "
              f"post_run_calls={len(a['post_run_calls'])} flags={len(a['flags'])}")
        for f in a["flags"]:
            inp = json.dumps(f.get("input"), ensure_ascii=False)[:160] if "input" in f else ""
            print(f"    - {f['why']} {f.get('match','')} @ {f.get('t')} {f.get('name','')} {inp}")

if __name__ == "__main__":
    main()
