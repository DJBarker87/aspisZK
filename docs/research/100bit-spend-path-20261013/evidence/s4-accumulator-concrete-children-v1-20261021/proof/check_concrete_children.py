#!/usr/bin/env python3
"""Pin the source leaves used by AccumulatorNewConcreteChildrenV4.

This checker validates source identity and the explicitly allowed carrier
translation. It is not a proof of Rust-to-Lean extraction correctness.
"""
from hashlib import sha256
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve()
ROOT = next(parent for parent in HERE.parents if (parent / "Cargo.toml").is_file())
FILES = {
    "transport": ROOT / "crates/aspis-r1-cost-probe/src/transport.rs",
    "qm31": ROOT / "crates/aspis-core/src/field.rs",
    "wide": ROOT / "crates/aspis-core/src/field/wide_exact.rs",
    "accepted_funs": ROOT / "docs/research/100bit-spend-path-20261013/evidence/tx1-caller-accepted-20261016/generated-accumulator/AspisR1PublicPreparation/Funs.lean",
    "proof": HERE.parents[1] / "sources/AccumulatorNewConcreteChildrenV4.lean",
}
EXPECTED = {
    "transport": "34af7f077fdae8147ebd79a44e7acb38395ec440115109c8fbfc654cb2c1e8c7",
    "qm31": "28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea",
    "wide": "6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b",
    "accepted_funs": "f4aee2661033aeaf820623a7decb3687e2617ae50a2ad4b41e78b253025a1de1",
}

def digest(p: Path) -> str:
    return sha256(p.read_bytes()).hexdigest()

for name, path in FILES.items():
    if not path.is_file():
        sys.exit(f"missing source: {path}")
    if name in EXPECTED and digest(path) != EXPECTED[name]:
        sys.exit(f"source pin mismatch: {name} {digest(path)}")

transport = FILES["transport"].read_text()
qm31 = FILES["qm31"].read_text()
wide = FILES["wide"].read_text()
funs = FILES["accepted_funs"].read_text()
proof = FILES["proof"].read_text()

for exact in (
    "pub fn folds(self) -> usize { if self == Self::S1 { 1 } else { 2 } }",
    "pub fn final_len(self) -> usize { 1024 >> (2*self.folds()) }",
):
    if exact not in transport:
        sys.exit(f"transport body token missing: {exact}")

qzero = re.search(r"pub const ZERO: QM31 = QM31 \{.*?\n    \};", qm31, re.S)
qone = re.search(r"pub const ONE: QM31 = QM31 \{.*?\n    \};", qm31, re.S)
wzero = re.search(r"pub const ZERO: Self = Self \{.*?\n    \};", wide, re.S)
if not (qzero and qone and wzero):
    sys.exit("could not locate exact source constants")
for token in ("M31(0)",):
    if token not in qzero.group(0):
        sys.exit("QM31::ZERO source value mismatch")
for token in ("M31(1)",):
    if token not in qone.group(0):
        sys.exit("QM31::ONE source value mismatch")
if "QM31::ZERO" not in wzero.group(0):
    sys.exit("WideExact::ZERO source value mismatch")

for exact in (
    "def transport.Variant.Insts.CoreCmpPartialEqVariant.eq",
    "let self1 := read_discriminant self",
    "def transport.Variant.folds (self : transport.Variant) : Result Std.Usize := do",
    "let b ←\n    transport.Variant.Insts.CoreCmpPartialEqVariant.eq self\n      transport.Variant.S1",
    "def transport.Variant.final_len\n  (self : transport.Variant) : Result Std.Usize := do",
    "let i ← transport.Variant.folds self\n  let i1 ← 2#usize * i\n  1024#usize >>> i1",
    "def aspis_core.field.QM31.ZERO : aspis_core.field.QM31 :=\n  { c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }",
    "def aspis_core.field.WideExact.ZERO : aspis_core.field.WideExact :=\n  { c0 := aspis_core.field.QM31.ZERO, c1 := aspis_core.field.QM31.ZERO }",
    "def aspis_core.field.QM31.ONE : aspis_core.field.QM31 :=\n  { c0 := { a := 1#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 }",
):
    if exact not in funs:
        sys.exit(f"accepted transparent generated owner missing: {exact}")

for exact in (
    "inductive SourceVariant where",
    "def variantToSource (v : Variant) : SourceVariant :=",
    "def sourceQMToCurrent (x : SourceQM31) : QM :=",
    "def sourceWideToCurrent (x : SourceWideExact) : Wide :=",
    "def sourceVariantEq (x y : SourceVariant) : Result Bool := do",
    "let x1 := match x with | .S1 => 0#isize | .S2 => 1#isize | .D => 2#isize",
    "let y1 := match y with | .S1 => 0#isize | .S2 => 1#isize | .D => 2#isize",
    "def sourceFinalLen (v : Variant) : Result Usize := do",
    "let i1 ← 2#usize * i",
    "1024#usize >>> i1",
    "def sourceQMZero : SourceQM31 :=",
    "def sourceQMOne : SourceQM31 :=",
    "def sourceWideZero : SourceWideExact :=",
    "(filled : Usize → QM → Result",
    "sourceFinalLen sourceZeroQResult filled sourceZeroWideResult sourceOneQResult",
):
    if exact not in proof:
        sys.exit(f"current-carrier source cut mismatch: {exact}")
if "FunsExternal" in proof or "filled_success_length" in proof:
    sys.exit("proof imports/uses allocator external axioms or unnecessary allocator theorem")

print("PASS: exact source pins, selected generated-owner declarations, and current-carrier leaf cut")
print("LIMIT: checker does not establish Charon/Aeneas semantic correctness or allocator behavior")
