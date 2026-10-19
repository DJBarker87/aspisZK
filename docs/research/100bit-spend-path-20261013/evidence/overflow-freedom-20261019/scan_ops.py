#!/usr/bin/env python3
"""Inventory failure-capable operations in Aeneas-generated Funs.lean files.

For each `def`, list every monadic (`←`) operation whose translation can
return `fail`: checked +, -, *, /, %, shifts, indexing/update, slice range
indexing, Vec index, unwrap/massert. `lift (...)` operations are total and
are not listed. Usage: scan_ops.py <Funs.lean>... ; prints JSON."""
import json, re, sys, hashlib

ARITH = re.compile(r"←\s*(\(?[A-Za-z0-9_.#«»\[\]]+\)?)\s*(\+|-|\*|/|%|>>>|<<<)\s*([A-Za-z0-9_.#«»]+)\s*$")
CALLS = [
    ("index", re.compile(r"←\s*(Array\.index_usize|Slice\.index_usize)\b")),
    ("update", re.compile(r"←\s*(Array\.update|Slice\.update)\b")),
    ("range_index", re.compile(r"←\s*core\.slice\.index\.Slice\.index\b")),
    ("vec_index", re.compile(r"←\s*alloc\.vec\.Vec\.(index|index_mut)\b")),
    ("unwrap", re.compile(r"←\s*core\.(option\.Option|result\.Result)\.(unwrap|expect)\b")),
    ("massert", re.compile(r"\bmassert\b")),
]
DEF = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:partial\s+)?def\s+([^\s]+)")

def is_const(tok):
    return bool(re.fullmatch(r"\(?\d+#[iu]\w+\)?", tok))

def scan(path):
    text = open(path, encoding="utf-8").read()
    out = {}
    cur = None
    for ln, line in enumerate(text.splitlines(), 1):
        m = DEF.match(line.strip()) if line.startswith(("def", "@[", "noncomputable", "partial")) else None
        if m:
            cur = m.group(1)
            out.setdefault(cur, [])
        if cur is None:
            continue
        a = ARITH.search(line)
        if a:
            l, op, r = a.groups()
            kind = {"+": "add", "-": "sub", "*": "mul", "/": "div", "%": "rem",
                    ">>>": "shr", "<<<": "shl"}[op]
            const = is_const(l) and is_const(r)
            out[cur].append({"line": ln, "kind": kind, "lhs": l, "rhs": r,
                             "constant_operands": const})
            continue
        for kind, rx in CALLS:
            if rx.search(line):
                out[cur].append({"line": ln, "kind": kind, "text": line.strip()[:120]})
                break
    return {"file": path, "sha256": hashlib.sha256(text.encode()).hexdigest(),
            "functions": {k: v for k, v in out.items() if v}}

if __name__ == "__main__":
    print(json.dumps([scan(p) for p in sys.argv[1:]], indent=1))
