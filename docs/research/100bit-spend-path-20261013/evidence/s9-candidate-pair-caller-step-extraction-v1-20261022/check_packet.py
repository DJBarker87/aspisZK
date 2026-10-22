#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

manifest = json.loads((ROOT / "manifest.json").read_text())
for rel, expected in manifest["files"].items():
    p = ROOT / rel
    assert p.is_file(), f"missing {rel}"
    assert sha(p) == expected, f"hash mismatch: {rel}"

for p in ROOT.rglob("*"):
    if not p.is_file():
        continue
    assert p.suffix.lower() not in {
        ".olean", ".ilean", ".o", ".a", ".so", ".dylib", ".rlib", ".exe",
    }, f"compiled artifact present: {p.relative_to(ROOT)}"
    assert b"\x00" not in p.read_bytes(), f"non-text/binary payload: {p.relative_to(ROOT)}"

sourcecheck = subprocess.run(
    [sys.executable, str(ROOT / "input/check_sourcecut.py")],
    cwd=ROOT / "input", check=False, capture_output=True, text=True,
)
assert sourcecheck.returncode == 0, sourcecheck.stdout + sourcecheck.stderr

llbc_path = ROOT / "attempt2/reused-charon/pair-caller-step.llbc"
llbc = json.loads(llbc_path.read_text())
assert llbc["has_errors"] is False
crate = llbc["translated"]
assert len(crate["fun_decls"]) == 175
assert len(crate["type_decls"]) == 57
assert len(crate["ordered_decls"]) == 63

def item_path(decl):
    return decl.get("item_meta", {}).get("name") if decl.get("item_meta") else None

def has_suffix(decl, suffix):
    p = item_path(decl)
    if not p:
        return False
    return any(part.get("Ident", [None])[0] == suffix for part in p)

decls = crate["fun_decls"]
for suffix in (
    "pair_step_root", "pair_s2_libra_parts_projection",
    "factored_s2_libra_weights", "twofold_libra_weights",
):
    assert any(has_suffix(d, suffix) for d in decls), f"LLBC declaration absent: {suffix}"

funs = ROOT / "attempt2/aeneas/generated/AspisR1S9PairCallerStepV1/Funs.lean"
external = ROOT / "attempt2/aeneas/generated/AspisR1S9PairCallerStepV1/FunsExternal_Template.lean"
fun_text, ext_text = funs.read_text(), external.read_text()
for needle in (
    "def weights.pair_step_root", "def weights.Weights.pair_s2_libra_parts_projection",
    "def weights.Weights.pair_s2_libra_parts_projection_loop.body",
    "def weights.factored_s2_libra_weights",
    "then weights.factored_s2_libra_weights ap0 ap1 self.extra",
    "else weights.twofold_libra_weights low self.extra",
    "let we1 ← weights.field f j", "let we3 ← field.WideExact.mul we1 we2",
    "let we4 ← field.WideExact.add we we3", "let a ← Array.update parts 4#usize we4",
):
    assert needle in fun_text, f"generated caller shape missing: {needle}"
for needle in (
    "axiom field.QM31.mul", "axiom field.QM31.square",
    "axiom field.WideExact.add", "axiom field.WideExact.mul",
    "axiom field.WideExact.mul_m31", "axiom field.WideExact.mul_qm31",
    "axiom weights.field", "axiom weights.twofold_libra_weights",
):
    assert needle in ext_text, f"expected raw diagnostic boundary missing: {needle}"
assert ext_text.count("axiom ") == 8

charon = json.loads((ROOT / "attempt2/reused-charon/command.json").read_text())
aeneas = json.loads((ROOT / "attempt2/aeneas/receipt.json").read_text())
assert charon["candidate_weights_sha256"] == manifest["candidate_weights_sha256"]
assert charon["frozen_weights_sha256"] == manifest["frozen_weights_sha256"]
assert charon["limits"] == {
    "memory.high": str(2 * 1024**3),
    "memory.max": str(4 * 1024**3),
    "memory.swap.max": "0",
}
assert aeneas["exit_status"] == 0 and not aeneas["timed_out"]
assert aeneas["reused_llbc_sha256"] == sha(llbc_path)
assert aeneas["limits"] == charon["limits"]
assert all(aeneas["source_function_present"].values())

print("PASS: candidate source pins and pair-body identity")
print("PASS: Charon LLBC declarations/shape and exact LLBC hash")
print("PASS: Aeneas generated caller-step declarations and opaque diagnostic boundaries")
print("PASS: scoped receipts, resource caps, and source-only packet")
