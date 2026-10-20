#!/usr/bin/env python3
"""Check that the extraction cut preserves the current field carrier layout/constants.

This is deliberately a narrow source check. It does not claim arithmetic
equivalence for the opaque add/mul methods, which remain explicit Lean ops.
"""
from pathlib import Path
import hashlib, json, re

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[5]
pins = json.loads((ROOT / "input/source-pins.json").read_text())
actual_field = REPO / "crates/aspis-core/src/field.rs"
actual_wide = REPO / "crates/aspis-core/src/field/wide_exact.rs"
cut = ROOT / "input/src/lib.rs"

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def compact(s):
    return re.sub(r",(?=})", "", re.sub(r"\s+", "", s)).rstrip(",")

def item_body(src, marker):
    i = src.index(marker)
    start = src.index("{", i)
    depth = 0
    for j in range(start, len(src)):
        if src[j] == "{": depth += 1
        elif src[j] == "}":
            depth -= 1
            if depth == 0:
                return src[start + 1:j]
    raise ValueError(marker)

field = actual_field.read_text()
wide = actual_wide.read_text()
cut_src = cut.read_text()

for rel, path in [
    ("crates/aspis-core/src/field.rs", actual_field),
    ("crates/aspis-core/src/field/wide_exact.rs", actual_wide),
]:
    expected = pins["source_files"][rel]
    got = sha(path)
    assert got == expected, f"source pin mismatch {rel}: {got} != {expected}"

def fields(src, marker):
    body = item_body(src, marker)
    return re.findall(r"(?:pub\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*:\s*([A-Za-z_][A-Za-z0-9_:]*)\s*,?", body)

shapes = {
    "CM31": [("a", "M31"), ("b", "M31")],
    "QM31": [("c0", "CM31"), ("c1", "CM31")],
    "WideExact": [("c0", "QM31"), ("c1", "QM31")],
}
source_markers = {
    "M31": "pub struct M31(",
    "CM31": "pub struct CM31",
    "QM31": "pub struct QM31",
    "WideExact": "pub struct WideExact",
}
cut_markers = {
    "M31": "pub struct M31(",
    "CM31": "pub struct CM31",
    "QM31": "pub struct QM31",
    "WideExact": "pub struct WideExact",
}
for name, expected in shapes.items():
    src = field if name != "WideExact" else wide
    actual = fields(src, source_markers[name])
    candidate = fields(cut_src, cut_markers[name])
    assert actual == expected, (name, "unexpected pinned source shape", actual)
    assert candidate == expected, (name, "candidate shape mismatch", candidate)
for src, label in [(field, "production"), (cut_src, "candidate")]:
    assert re.search(r"pub\s+struct\s+M31\s*\(\s*pub\s+u32\s*\)\s*;", src), f"{label} M31 tuple layout mismatch"

for typ, source in [("QM31", field), ("WideExact", wide)]:
    if typ == "QM31":
        actual = compact(item_body(source, "pub const ZERO: QM31 ="))
        candidate = compact(item_body(cut_src, "pub const ZERO: Self ="))
    else:
        actual = compact(item_body(source[source.index("impl WideExact"):], "pub const ZERO: Self ="))
        candidate = compact(item_body(cut_src[cut_src.index("impl WideExact"):], "pub const ZERO: Self ="))
    assert actual == candidate, (typ, "ZERO differs", actual, candidate)
actual = compact(item_body(field, "pub const ONE: QM31 ="))
candidate = compact(item_body(cut_src, "pub const ONE: Self ="))
assert actual == candidate, ("QM31", "ONE differs", actual, candidate)

print(json.dumps({
    "status": "PASS",
    "production_field_sha256": sha(actual_field),
    "production_wide_exact_sha256": sha(actual_wide),
    "candidate_lib_sha256": sha(cut),
    "checked": ["M31/CM31/QM31/WideExact field order and types", "QM31.ZERO", "QM31.ONE", "WideExact.ZERO"],
    "excluded": ["WideExact.add/mul behavior; explicit operations boundary"],
}, indent=2))
