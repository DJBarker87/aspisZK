import NMS_242Tail
set_option autoImplicit false
noncomputable section
namespace NMS_242TailFactor
open Aeneas Aeneas.Std Result AdapterRw NMS_OwnedPackets NMS_RowSpec242
variable {Ambient : Type}
/-- Exact emitted-style suffix after a successful scanner reply. -/
def literal (ops : Ops) (inputs : List Nat) (request : Request) (auth : Auth) (scanned : Scanned) :
 NMS_Owned242.Run Ambient (core.result.Result Validated PE) := do
 let reply ← NMS_Owned242.reconstruct ops inputs request auth scanned.candidate
 let flow ← core.result.Result.Insts.CoreOpsTry.branch reply
 match flow with
 | .Continue statement => ok (.Ok ⟨statement,scanned.proofLength⟩)
 | .Break residual =>
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
   Validated (core.convert.FromSame PE) residual

theorem factor (ops : Ops) (inputs : List Nat) (request : Request) (auth : Auth) (scanned : Scanned) :
 NMS_242Tail.owned (Ambient := Ambient) ops inputs request auth scanned =
 literal ops inputs request auth scanned := by
 unfold NMS_242Tail.owned NMS_TryFold.step literal
 cases h : NMS_Owned242.reconstruct ops inputs request auth scanned.candidate with
 | mk result events =>
  cases result with
  | ok reply => cases reply <;> rfl
  | fail _ => rfl
  | div => rfl
#print axioms factor
end NMS_242TailFactor
