#!/usr/bin/env python3
"""X3 cascade driver (lead's rule of 2026-11-12). Loop:
  1. fv_x3_pipeline4.sh (text steps, gate, hardlinks), then the Lean 4.32.0 compile of plan4-table.tsv into
     W/x3/map4-old in ONE fv_slot scope (attempt X3-C-cas-<n>), resumed by source key;
  2. stop when AspisFailureBoundModel compiles (exit 0), or when the gate reports a violation;
  3. for every module that failed (exit not 0, not skipped):
     - needed constants of the module (uses/top_closure.tsv.gz) = 0 and the first error is a missing name
       (unknown identifier / constant / namespace)  -> module added to W/x3/omit4.txt;
     - module has needed constants: the declarations enclosing every error line; if none of them is needed and the
       first error is a missing name -> those declarations added to W/x3/drop-decls4.tsv;
     - otherwise STOP (a needed declaration fails, or an error of another kind) and write STOP.txt.
Every addition is a row of W/x3/omit-drop-additions.tsv:
  item, kind (omit|drop), step, first error, missing name it depended on, needed constants in the module.
Usage: fv_x3_cascade.py <top_closure.tsv> <top_closure_modules.tsv> [max-iterations]
"""
import os, re, subprocess, sys

W = "/home/dombarker/project-offloads/future-version-20261111"
X = W + "/x3"
L = "/home/dombarker/project-offloads/codex-cx-replay-l187-20261109"
top, topm = sys.argv[1], sys.argv[2]
maxit = int(sys.argv[3]) if len(sys.argv) > 3 else 25
needed = {}  # module -> set of constant names
for l in open(top):
    m, c = l.rstrip("\n").split("\t")[:2]
    needed.setdefault(m, set()).add(c)
HEAD = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial)\s+)*"
                  r"(def|theorem|lemma|abbrev|structure|inductive|instance|opaque|axiom|class)\s+([^\s(:{\[]+)")
MISSING = re.compile(r"[Uu]nknown (identifier|constant|namespace)|does not contain|unknown declaration")
ADD = X + "/omit-drop-additions.tsv"
if not os.path.exists(ADD):
    open(ADD, "w").write("item\tkind\tstep\tfirst_error\tdepends_on\tneeded_constants_in_module\n")


def run(cmd):
    return subprocess.run(cmd, shell=True, text=True, capture_output=True)


def decl_of(lines, ln):
    for k in range(ln - 1, -1, -1):
        h = HEAD.match(lines[k])
        if h:
            return h.group(2)
    return None


def is_needed(m, short):
    for c in needed.get(m, ()):
        if c.endswith("." + short) or ("." + short + ".") in c:
            return True
    return False


for it in range(1, maxit + 1):
    r = run(f"bash {X}/bin/fv_x3_pipeline4.sh")
    if r.returncode != 0:
        open(X + "/STOP.txt", "w").write(f"step {it}: pipeline failed\n{r.stdout[-2000:]}{r.stderr[-2000:]}"); sys.exit(1)
    gate = [l.rstrip("\n").split("\t") for l in open(X + "/closure/plan4-gate.tsv")][1:]
    if any(g[3] for g in gate):
        open(X + "/STOP.txt", "w").write(f"step {it}: gate violation\n"); sys.exit(1)
    att = f"X3-C-cas{os.environ.get('X3_CASTAG', '')}-{it}"
    cmd = (f"bash {W}/fv_slot.sh {att} 14400 env X3_TCD=$HOME/.elan/toolchains/leanprover--lean4---v4.32.0 "
           f"X3_LPBASE={X}/l187-carried4:{L}/base_ref bash {X}/bin/fv_x3_closure_compile.sh "
           f"{X}/closure/plan4-table.tsv {X}/map4-old")
    run(cmd)
    res = {l.split("\t")[0]: l.rstrip("\n").split("\t") for l in open(X + "/map4-old/result.tsv")}
    with open(X + "/cascade-steps.txt", "a") as f:
        st = {}
        for v in res.values():
            k = v[1] if v[1] in ("0", "skipped") else "failed"; st[k] = st.get(k, 0) + 1
        f.write(f"step {it} {att} {st}\n")
    if res.get("AspisFailureBoundModel", ["", ""])[1] == "0":
        open(X + "/CASCADE_DONE", "w").write(f"step {it}\n"); sys.exit(0)
    failed = [m for m, v in res.items() if v[1] not in ("0", "skipped")]
    if not failed:
        open(X + "/STOP.txt", "w").write(f"step {it}: no failure but model not compiled\n"); sys.exit(1)
    plan = {l.split("\t")[0]: l.split("\t")[2] for l in list(open(X + "/closure/plan4-table.tsv"))[1:]}
    adds = []
    for m in failed:
        log = open(f"{X}/map4-old/log/{m}.log", errors="replace").read()
        errs = re.findall(r"\.lean:(\d+):\d+: error(?:\([\w.]+\))?: ?([^\n]*)", log)
        first = errs[0][1] if errs else "(no error line)"
        if first.startswith("overloaded"):
            # an overload error lists each alternative's error on the following lines; use the missing name there
            k = log.find("overloaded")
            inner = re.search(r"([Uu]nknown (?:identifier|constant|namespace) `[^`]+`)", log[k:k + 800])
            if inner:
                first = "overloaded: " + inner.group(1)
        dep = re.search(r"`([^`]+)`", first)
        dep = dep.group(1) if dep else ""
        nn = len(needed.get(m, ()))
        if "unknown namespace" in first:
            # tie-breaker of 2026-11-12: a failure at an `open X` line means X must be kept and trimmed; never omit.
            # If X is an omit addition of this cascade (not in the lead's list), reverse it: X goes to the keep list,
            # its failing declarations are dropped at the next step. Otherwise stop and report.
            ns = re.search(r"`([^`]+)`", first).group(1).split(".")[-1]
            base_omit = {l.strip() for l in open(os.environ["X3_LIB"] + "/OMIT_MODULES.txt") if l.strip()}
            cur = [l.strip() for l in open(X + "/omit4.txt") if l.strip()]
            if ns in cur and ns not in base_omit:
                open(X + "/omit4.txt", "w").write("\n".join(c for c in cur if c != ns) + "\n")
                open(X + "/keep4.txt", "a").write(ns + "\n")
                with open(ADD, "a") as f:
                    f.write(f"{ns}\tomit REVERSED (kept: {m} opens its namespace)\t{it}\t{first[:200]}\t\t0\n")
                continue
            open(X + "/STOP.txt", "w").write(f"step {it}: {m}: open of a removed namespace (keep-and-trim case): {first}\n")
            sys.exit(3)
        if not MISSING.search(first):
            open(X + "/STOP.txt", "w").write(f"step {it}: {m}: first error is not a missing name: {first}\n"); sys.exit(1)
        keep = {l.strip() for l in open(X + "/keep4.txt")} if os.path.exists(X + "/keep4.txt") else set()
        if nn == 0 and m not in keep:
            adds.append((m, "omit", first, dep, nn)); continue
        src = open(plan[m], errors="replace").read().split("\n")
        decls = sorted({d for ln, _ in errs if (d := decl_of(src, int(ln)))})
        need = [d for d in decls if is_needed(m, d)]
        if need or not decls:
            open(X + "/STOP.txt", "w").write(f"step {it}: NEEDED declaration fails: {m} {need or '(no enclosing decl)'}: {first}\n")
            sys.exit(2)
        for d in decls:
            adds.append((f"{m}\t{d}", "drop", first, dep, nn))
    with open(ADD, "a") as f, open(X + "/omit4.txt", "a") as om, open(X + "/drop-decls4.tsv", "a") as dd:
        for item, k, first, dep, nn in adds:
            f.write(f"{item.replace(chr(9), '.')}\t{k}\t{it}\t{first[:300]}\t{dep}\t{nn}\n")
            (om if k == "omit" else dd).write(item + "\n")
open(X + "/STOP.txt", "w").write("max iterations\n")
