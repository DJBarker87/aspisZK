#!/usr/bin/env python3
"""Validate immutable source pins and wrapper-order evidence for this packet."""
from hashlib import sha256
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parent
def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()

def compact(text: str) -> str:
    return re.sub(r"\s+", "", text)

receipt = json.loads((ROOT / "producer/receipt.json").read_text())
expected = {
    "sources/S4Tx2AuthenticatedWrapperCutV1.lean": "f5d3b4d75b71e9ec203bb26ccdf034ede4d22a4cd86f368c9365895cbc33a031",
    "source-pins/Funs.lean": "b3aa665deadedac1f04233f5535bce0774cfed34e6ee7f979657982504d97c2b",
    "source-pins/candidate-current.rs": "5164975df10f79e9810f9321b8130a9865eb9bb9b6b9de7011f4359ece98c794",
}
for rel, want in expected.items():
    got = digest(ROOT / rel)
    assert got == want, f"{rel}: {got} != {want}"
assert digest(ROOT / "source-pins/Stage2ContinuationQueryLoop.lean") == \
    "c398ba41273939ac739a064eee492976988027ff1b1d6f33657480b17aed0def"
imports = json.loads((ROOT / "producer/import-pins.json").read_text())
assert imports["selected_object_sha256"] == \
    "20a8d68464f20012572d37f1228045ac2a42a5776e3d5f8281f7180b24c0d450"
assert receipt["source_sha256"] == expected["sources/S4Tx2AuthenticatedWrapperCutV1.lean"]
assert receipt["exit_status"] == 0
assert receipt["object_sha256"] == "3bba4483138ad020a0b01c7d57a10a2ec3c4e2674098196f58f897d3e4e3234d"
assert receipt["compiler_sha256"] == "1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554"
assert receipt["process_swaps"] == 0
axioms = " ".join(receipt["axiom_lines"])
for axiom in ("propext", "Classical.choice", "Quot.sound"):
    assert axiom in axioms, f"missing expected standard axiom {axiom}"
assert "sorryAx" not in axioms

lean = (ROOT / "sources/S4Tx2AuthenticatedWrapperCutV1.lean").read_text()
cut_start = lean.index("def tx2AuthenticatedOperationCut")
cut_end = lean.index("\nprivate theorem bind_success", cut_start)
cut_body = lean[cut_start:cut_end]
expected_cut = compact("""def tx2AuthenticatedOperationCut {H : Type}
    (inst : aspis_core.digest.Digest32 H)
    (parseShape : Slice U8 → Result (core.result.Result Variant Error))
    (mark : Option (verifier.Phase → Result Unit) → verifier.Phase → Result Unit)
    (tx2Common : aspis_core.digest.Digest32 H → Slice U8 → Slice U8 → Slice U8 → H →
      Option (verifier.Phase → Result Unit) → Result Accepted)
    (public_bytes proof checkpoint : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) : Result Accepted := do
  let r ← parseShape proof
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | Aeneas.Std.core.ops.control_flow.ControlFlow.Continue _ => do
    mark obs verifier.Phase.Parsed
    tx2Common inst public_bytes proof checkpoint hash obs
  | Aeneas.Std.core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame Error) residual""")
assert compact(cut_body) == expected_cut, "operation cut body/signature changed"

funs = (ROOT / "source-pins/Funs.lean").read_text()
start = funs.index("def verifier.candidate.tx2_authenticated\n")
end = funs.index("\nend AspisR1Stage2", start)
generated = compact(funs[start:end])
expected_generated = compact("""def verifier.candidate.tx2_authenticated
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8)
  (checkpoint : Slice Std.U8) (hash : H)
  (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result Unit verifier.Error)
  := do
  let r ← verifier.candidate.parse_shape proof
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    verifier.mark obs verifier.Phase.Parsed
    verifier.candidate.tx2_common aspis_coredigestDigest32Inst public_bytes
      proof checkpoint hash obs
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame verifier.Error) residual""")
assert generated == expected_generated, "complete emitted generated wrapper body differs"
generated_body = compact(funs[start:end].split(":= do", 1)[1])
cut_body_only = compact(cut_body.split(":= do", 1)[1])
callee_map = [
    ("verifier.candidate.parse_shape", "parseShape"),
    ("verifier.mark", "mark"),
    ("verifier.candidate.tx2_common aspis_coredigestDigest32Inst", "tx2Common inst"),
    ("core.ops.control_flow.ControlFlow", "Aeneas.Std.core.ops.control_flow.ControlFlow"),
    ("verifier.Error", "Error"),
]
for rust_name, cut_name in callee_map:
    generated_body = generated_body.replace(compact(rust_name), compact(cut_name))
generated_body = generated_body.replace("ControlFlow.Continue_=>", "ControlFlow.Continue_=>do")
assert generated_body == cut_body_only, "operation cut differs after explicit callee/type map"
rust = (ROOT / "source-pins/candidate-current.rs").read_text()
start = rust.index("pub fn tx2_authenticated<")
end = rust.index("\n}", start)
rust_body = compact(rust[start:end + 2])
expected_rust = compact("""pub fn tx2_authenticated<H: Digest32>(public_bytes: &[u8], proof: &[u8], checkpoint: &[u8], hash: H, obs: Observer) -> Result<(), Error> {
    parse_shape(proof)?;
    mark(obs, Phase::Parsed);
    tx2_common(public_bytes, proof, checkpoint, hash, obs)
}""")
assert rust_body == expected_rust, "complete current Rust wrapper body differs"
assert not list(ROOT.rglob("*.olean")), "compiled Lean object must not be in this source-only packet"
print("PASS: source pins, launch receipt, standard axiom audit, and wrapper order")
