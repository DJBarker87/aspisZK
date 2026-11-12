#!/usr/bin/env python3
"""X3: import closure of a Lean root module, down to (not including) the external packages.

Reads only. Resolution order for a module name M: each source dir in turn (M with dots as slashes + .lean).
External prefixes (Mathlib, Aeneas, toolchain, Mathlib's dependencies) end the walk. A module that is neither
external nor found in a source dir is reported as 'unresolved' together with whether an object of that name
exists under the given object dirs (for example a vendored package present only as objects).

Usage: fv_x3_closure.py <root-module> <out.tsv> <order.txt> --src DIR [--src DIR ...] [--obj DIR ...]
Columns of out.tsv: module, source_dir_tag, path, lines, sha256, aeneas_import, aeneas_mention,
  external_imports, closure_imports, kind_hint_inputs
"""
import argparse, hashlib, os, re, sys

EXTERNAL = ("Mathlib", "Aeneas", "AeneasMeta", "Batteries", "Aesop", "Qq", "Init", "Lean", "Std", "Lake",
            "Plausible", "ProofWidgets", "ImportGraph", "LeanSearchClient", "Cli")

IMPORT_RE = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(.*)$")
# Aeneas mention: the library namespaces and its scalar/result vocabulary.
AENEAS_RE = re.compile(r"\b(Aeneas\.|open\s+Aeneas|Std\.U8|Std\.U16|Std\.U32|Std\.U64|Std\.U128|Std\.Usize|"
                       r"Std\.I32|Std\.I64|Std\.Result|Std\.Slice|Std\.Array|Std\.Vec|Std\.Scalar|"
                       r"\bU8\b|\bU32\b|\bU64\b|\bUsize\b|\bScalarTy\b|\bResult\.ok\b|\.ok\b|\.fail\b|"
                       r"\bprogress\b|\bscalar_tac\b|alloc\.vec\.Vec|core\.)")


def is_external(m):
    return m.split(".")[0] in EXTERNAL


def strip_comments(text):
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def imports_of(text):
    out = []
    body = strip_comments(text)
    for line in body.splitlines():
        s = line.strip()
        if not s:
            continue
        m = IMPORT_RE.match(line)
        if m:
            # `import all M` (module system): `all` is a keyword, not a module
            out += [t for t in m.group(1).split() if t != "all"]
            continue
        if s.startswith(("module", "prelude", "set_option", "#")):
            continue
        if not s.startswith("import"):
            break
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("root"); ap.add_argument("out"); ap.add_argument("order")
    ap.add_argument("--src", action="append", default=[])
    ap.add_argument("--obj", action="append", default=[])
    a = ap.parse_args()
    srcs = []
    for s in a.src:
        tag, d = s.split("=", 1)
        srcs.append((tag, d))
    info, seen, stack, order = {}, set(), [a.root], []

    def resolve(m):
        rel = m.replace(".", "/") + ".lean"
        for tag, d in srcs:
            p = os.path.join(d, rel)
            if os.path.isfile(p):
                return tag, p
        return None, None

    # iterative DFS post-order for a dependency order
    visiting = set()

    def visit(m):
        if m in seen:
            return
        work = [(m, False)]
        while work:
            cur, done = work.pop()
            if done:
                if cur not in seen:
                    seen.add(cur); order.append(cur)
                continue
            if cur in seen or cur in visiting:
                continue
            visiting.add(cur)
            tag, p = resolve(cur)
            if p is None:
                objs = [o for o in a.obj if os.path.isfile(os.path.join(o, cur.replace(".", "/") + ".olean"))]
                info[cur] = dict(tag="unresolved", path="", lines=0, sha="", ai=0, am=0, ext=[], loc=[],
                                 obj=";".join(objs))
                seen.add(cur); order.append(cur)
                continue
            raw = open(p, "rb").read()
            text = raw.decode("utf-8", "replace")
            imps = imports_of(text)
            ext = [i for i in imps if is_external(i)]
            loc = [i for i in imps if not is_external(i)]
            info[cur] = dict(tag=tag, path=p, lines=text.count("\n"), sha=hashlib.sha256(raw).hexdigest(),
                             ai=int(any(i.split(".")[0] in ("Aeneas", "AeneasMeta") for i in imps)),
                             am=len(AENEAS_RE.findall(strip_comments(text))), ext=ext, loc=loc, obj="")
            work.append((cur, True))
            for i in reversed(loc):
                if i not in seen:
                    work.append((i, False))

    visit(a.root)
    with open(a.out, "w") as f:
        f.write("module\tsource\tpath\tlines\tsha256\taeneas_import\taeneas_mention_count\texternal_imports\t"
                "closure_imports\tobject_only_in\n")
        for m in order:
            d = info[m]
            f.write("\t".join([m, d["tag"], d["path"], str(d["lines"]), d["sha"], str(d["ai"]), str(d["am"]),
                               ",".join(d["ext"]), ",".join(d["loc"]), d["obj"]]) + "\n")
    with open(a.order, "w") as f:
        f.write("\n".join(order) + "\n")
    print(f"closure {len(order)} modules; unresolved {sum(1 for m in order if info[m]['tag']=='unresolved')}",
          file=sys.stderr)


if __name__ == "__main__":
    main()
