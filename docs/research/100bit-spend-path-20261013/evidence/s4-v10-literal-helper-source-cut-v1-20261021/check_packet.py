#!/usr/bin/env python3
"""Verify exact pinned V10 helper tokens and the focused Lean receipt."""
from pathlib import Path
import hashlib, json, re

P = Path(__file__).resolve().parent
RESEARCH = P.parents[1]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def body(path, name):
    text = path.read_text()
    match = re.search(
        r"^def " + re.escape(name) + r"\b.*?\s:= do\n(.*?)(?=^/(?:--|\*)|^theorem |^end |\Z)",
        text, re.M | re.S)
    assert match, f"missing do-body {name} in {path}"
    return match.group(1).rstrip()

def tokens(text):
    return re.findall(r"[A-Za-z_][A-Za-z0-9_\.]*|[0-9]+#(?:usize|u64)|:=|←|[^\s]", text)

for line in (P / "SHA256SUMS").read_text().splitlines():
    digest, name = line.split("  ", 1)
    assert sha(P / name) == digest, name
r = json.loads((P / "receipts/receipt.json").read_text())
assert r["schema"] == "focused-lean-receipt-v1" and r["exit_status"] == 0
assert r["peak_rss_bytes"] == 3756589056 and r["swap_bytes"] == 0
assert r["axioms"] == ["propext", "Classical.choice", "Quot.sound"]
assert sha(P / "sources/S4V10LiteralHelperSourceCutV1.lean") == r["source_sha256"]
assert sha(P / "extraction/FunsV10.lean") == r["generated_v10_funs_sha256"]
assert sha(Path(r["compiler"])) == r["compiler_sha256"]
assert not list(P.rglob("*.olean")), "binary artifacts are not part of this source-only packet"
for module, pin in r["direct_imports"].items():
    source_path = RESEARCH / pin["source_path"].split("docs/research/100bit-spend-path-20261013/", 1)[-1]
    assert sha(source_path) == pin["source_sha256"], module + " source"
    assert sha(Path(pin["object_path"])) == pin["object_sha256"], module + " object"

candidate = RESEARCH / "lean-candidates/s4-minimal-fixed-calls-v10-20261021/extraction/evidence/generated/AspisR1FastDotsMinimalFixedCallsV10/Funs.lean"
assert sha(candidate) == r["generated_v10_funs_sha256"]
source = P / "sources/S4V10LiteralHelperSourceCutV1.lean"
cut = body(source, "literalV10Helper")
emitted = body(P / "extraction/FunsV10.lean", "fast_dots.four_dots_one")
# These are the named operation slots used in the typed adapter. All other
# tokens, including control flow, indices, arithmetic, and effect order, must
# match the retained generated body exactly.
replacements = [
    (r"fast_dots\.four_dots_one_loop0\s+iter\s+q\s+g\s+slot\s+limbs", "v10HeadLoop ops iter q g slot limbs"),
    (r"aspis_core\.field\.M31\.reduce_u64", "ops.m31ReduceU64"),
    (r"aspis_core\.field\.wide_exact\.WideExact\.from_limbs", "literalFromLimbs ops"),
    (r"fast_pairing\.EbyKDot\.new", "ops.ebyKNew"),
    (r"aspis_core\.field\.QM31\.from_le_bytes", "literalQMFromBytes ops"),
    (r"fast_pairing\.EbyKDot\.push", "literalPush ops"),
    (r"fast_pairing\.EbyKDot\.finish", "literalFinish ops"),
    (r"aspis_core\.field\.wide_exact\.WideExact\.add", "literalAdd ops"),
]
for pattern, replacement in replacements:
    emitted, count = re.subn(pattern, replacement, emitted)
    assert count > 0, f"pinned generated operation did not occur: {pattern}"
assert tokens(emitted) == tokens(cut), "literal helper cut differs beyond named operation slots"
lean = Path(r["compiler"])
assert lean.name == "lean" and "v4.32.0" in str(lean)
log = (P / "receipts/compile.log").read_text()
assert "literal_helper_eq_fixed" in log and "8.74 real" in log and "0  swaps" in log
print("PASS: source-only packet hashes, focused Lean receipt, standard axioms")
print("PASS: exact V10 helper body token match after named operation-slot substitutions")
print("Scope: typed source-cut theorem only; no Rust std/from_fn or frozen-source adoption claim")
