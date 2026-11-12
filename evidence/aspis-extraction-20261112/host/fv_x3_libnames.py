#!/usr/bin/env python3
"""X3 static probe (NOT an elaboration): which Rust-library paths does the raw Aeneas emission reference, and does
the native Aeneas Lean library source declare a Lean name for each?

A reference is a token core.X / alloc.X / std.X in the emitted text (comments and string literals removed). It
resolves when the library declares a name N (namespace prefix included) with N == ref or N ending in "." + ref, or,
for a field/constructor/method reference, when the reference minus its last component resolves that way to a
structure, class or inductive. Declarations are read with a regular expression (def, theorem, abbrev, structure,
inductive, class, instance, opaque, axiom, impl_def, irreducible_def, and the scalar templates `scalar`/`uscalar`/
`iscalar` with 'S expanded over the scalar names; structure fields are NOT parsed), so a miss means
"not found by this reader", to be confirmed by a compile.

Usage: fv_x3_libnames.py <native-lib-dir> <out.tsv> <scope>=<raw-dir> [...]
"""
import os, re, sys

DECL = re.compile(r"^\s*(?:(u|i)?scalar\s+)?(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|public)\s+)*"
                  r"(def|theorem|lemma|abbrev|structure|inductive|class|instance|opaque|axiom|impl_def|irreducible_def)\s+"
                  r"(?:\([^)]*\)\s*)?([A-Za-z_][\w.']*)", re.M)
USC = ["U8", "U16", "U32", "U64", "U128", "Usize"]
ISC = ["I8", "I16", "I32", "I64", "I128", "Isize"]
CTOR = re.compile(r"^\s*\|\s*([A-Za-z_][\w']*)", re.M)
FIELD = re.compile(r"^\s{2,}([a-z_][\w']*)\s*:", re.M)
REF = re.compile(r"(?<![\w.])((?:core|alloc|std)\.[A-Za-z_][\w.']*)")


def strip(t):
    t = re.sub(r"/-.*?-/", " ", t, flags=re.S)
    t = re.sub(r"--[^\n]*", "", t)
    return re.sub(r'"(?:[^"\\]|\\.)*"', '""', t)


def lib_names(d):
    names, types = set(), set()
    for root, _, files in os.walk(d):
        for fn in files:
            if not fn.endswith(".lean"):
                continue
            t = strip(open(os.path.join(root, fn), encoding="utf-8", errors="replace").read())
            # namespace tracking, line based
            ns = []
            for line in t.splitlines():
                s = line.strip()
                m = re.match(r"namespace\s+([\w.]+)", s)
                if m:
                    ns.append(m.group(1)); continue
                m = re.match(r"end\s+([\w.]+)\s*$", s)
                if m and ns and ns[-1] == m.group(1):
                    ns.pop(); continue
                m = DECL.match(line)
                if m:
                    base = m.group(3)
                    if "'S" in base:  # scalar template: 'S is replaced by each scalar name
                        sc = {"u": USC, "i": ISC}.get(m.group(1) or "", USC + ISC)
                        insts = [base.replace("'S", x) for x in sc]
                    else:
                        insts = [base]
                    for nm in insts:
                        full = ".".join(ns + [nm])
                        names.add(full); names.add(nm)
                        if m.group(2) in ("structure", "inductive", "class"):
                            types.add(full); types.add(nm)
    return names, types


def resolves(ref, names, types):
    def hit(r, pool):
        return r in pool or any(n.endswith("." + r) for n in pool)
    if hit(ref, names):
        return "declared"
    parts = ref.split(".")
    for k in range(len(parts) - 1, 1, -1):
        pre = ".".join(parts[:k])
        if hit(pre, types):
            return "member of " + pre
        if hit(pre, names):
            return "under declared " + pre
    return ""


def main():
    lib, out = sys.argv[1], sys.argv[2]
    names, types = lib_names(lib)
    blob = ""
    for root, _, files in os.walk(lib):
        for fn in files:
            if fn.endswith(".lean"):
                blob += strip(open(os.path.join(root, fn), encoding="utf-8", errors="replace").read()) + "\n"
    # speed: index by last component
    rows = []
    for arg in sys.argv[3:]:
        scope, d = arg.split("=", 1)
        refs = {}
        own = set()
        for fn in sorted(os.listdir(d)):
            if fn.endswith(".lean"):
                tt = strip(open(os.path.join(d, fn), encoding="utf-8", errors="replace").read())
                own |= {m[2] for m in DECL.findall(tt)}
        for fn in sorted(os.listdir(d)):
            if not fn.endswith(".lean"):
                continue
            t = strip(open(os.path.join(d, fn), encoding="utf-8", errors="replace").read())
            for r in REF.findall(t):
                r = r.rstrip(".")
                refs.setdefault(r, set()).add(fn)
        for r in sorted(refs):
            res = resolves(r, names, types)
            if not res and r in own:
                res = "declared by the emission's own Types/External template"
            if not res:
                parts = r.split(".")
                tail2 = ".".join(parts[-2:])
                if re.search(r"(?<![\w])" + re.escape(parts[-1]) + r"(?![\w])", blob):
                    res = "text only: last component '" + parts[-1] + "' occurs in the library (macro-generated or other form; compile needed)"
            rows.append((scope, r, res, ",".join(sorted(refs[r]))))
    with open(out, "w") as f:
        f.write("scope\treference\tnative_resolution\tfiles\n")
        for row in rows:
            f.write("\t".join(row) + "\n")
    miss = [r for r in rows if not r[2]]
    print(f"declared names {len(names)}; references {len(rows)}; unresolved {len(miss)}", file=sys.stderr)
    for r in miss:
        print("UNRESOLVED", *r, sep="\t", file=sys.stderr)


if __name__ == "__main__":
    main()
