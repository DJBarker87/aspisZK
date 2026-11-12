#!/usr/bin/env python3
"""X3 stage C pass 2 planning (reads only, writes tables).

  trim     <closure-modules.tsv> <out-list>
           kind (c) modules with a direct import of a kind (d) module (the modules the trim script changes)
  old      <closure-modules.tsv> <trimmed-src> <out.tsv>
           every kind (c) module whose closure reaches (d) (reaches_d = 1), dependency order; path = the trimmed
           copy when one exists, else the L187 source; closure_imports without (d) modules
  pass2    <closure-modules.tsv> <trimmed-src> <old-result.tsv> <out.tsv> <out-excluded.tsv>
           the carrier-free set: all kind (c) and (b) modules, minus every module that failed or was skipped in the
           old-toolchain recompile and everything downstream of it; same path and import rules as `old`
"""
import os, sys


def load(t):
    rows = [l.rstrip("\n").split("\t") for l in open(t)]
    h = rows[0]
    return [dict(zip(h, r)) for r in rows[1:]]


def imports(r):
    return [x for x in r["closure_imports"].split(",") if x]


def main():
    mode = sys.argv[1]
    rows = load(sys.argv[2])
    kind = {r["module"]: r["kind"] for r in rows}
    if mode == "trim":
        with open(sys.argv[3], "w") as f:
            for r in rows:
                if r["kind"] == "c" and any(kind[i] == "d" for i in imports(r)):
                    f.write(r["module"] + "\n")
        return
    tsrc = sys.argv[3]

    def path(r):
        p = os.path.join(tsrc, r["module"].replace(".", "/") + ".lean")
        return p if os.path.isfile(p) else r["path"]

    def file_imports(p):
        # imports of a trimmed copy, read from the file (closure modules only)
        out = []
        for l in open(p, encoding="utf-8", errors="replace"):
            s = l.strip()
            if s.startswith("import ") and s[7:].strip() in kind:
                out.append(s[7:].strip())
        return out

    def emit(sel, out):
        with open(out, "w") as f:
            f.write("module\tkind\tpath\tlines\tclosure_imports\n")
            for r in sel:
                src_imps = file_imports(path(r)) if path(r) != r["path"] else imports(r)
                imps = [i for i in src_imps if kind[i] != "d"]
                f.write(f"{r['module']}\t{r['kind']}\t{path(r)}\t{r['lines']}\t{','.join(imps)}\n")

    if mode == "old":
        emit([r for r in rows if r["kind"] == "c" and r["reaches_d"] == "1"], sys.argv[4])
        return
    if mode == "pass2":
        res = {l.split("\t")[0]: l.rstrip("\n").split("\t") for l in open(sys.argv[4])}
        bad = {m: ("old toolchain: exit " + v[1] + (" " + v[5] if len(v) > 5 else ""))
               for m, v in res.items() if v[1] != "0"}
        sel, excl = [], []
        for r in rows:  # dependency order
            m = r["module"]
            if r["kind"] not in ("b", "c"):
                continue
            if m in bad:
                excl.append((m, bad[m])); continue
            up = [i for i in imports(r) if kind[i] != "d" and i in bad]
            if up:
                bad[m] = "imports excluded " + up[0]
                excl.append((m, bad[m])); continue
            sel.append(r)
        emit(sel, sys.argv[5])
        with open(sys.argv[6], "w") as f:
            f.write("module\treason\n")
            for m, why in excl:
                f.write(f"{m}\t{why}\n")
        print("pass2", len(sel), "lines", sum(int(r["lines"]) for r in sel), "excluded", len(excl), file=sys.stderr)


if __name__ == "__main__":
    main()
