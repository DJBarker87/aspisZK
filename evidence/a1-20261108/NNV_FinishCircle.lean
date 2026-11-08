import NNV_ResultOkPort
import NNV_FinishCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_FinishCircle
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers

theorem returned (t : Transcript) (r : Record) (env : RSL.Env) (z : Point) (after : Transcript)
 (called : LIB_VLib.circleValue (t,r) env = .ok (z,after)) :
 (PreparedHashCode.run (NJM_CircleCode.source (LIB_VCode.digest env) t r)).2 = .ok (.Ok z,after) := by
 change LIB_VResult.value LIB_VCircle.project (.error .InvalidRow)
  (PreparedHashCode.run (LIB_VCircle.code (t,r) env)).2 = .ok (z,after) at called
 cases raw : (PreparedHashCode.run (LIB_VCircle.code (t,r) env)).2 with
 | fail e => rw [raw] at called; cases called
 | div => rw [raw] at called; cases called
 | ok pair =>
  rcases pair with ⟨reply,post⟩
  cases reply with
  | Err e => rw [raw] at called; cases called
  | Ok point =>
   rw [raw] at called
   have same : (point,post)=(z,after) := Except.ok.inj called
   cases same
   exact raw
#print axioms returned
end AspisR1.NNV_FinishCircle
end
