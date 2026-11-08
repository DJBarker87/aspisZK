import NNV_ResultOkPort
import NNV_PrepareFrontCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_FinishTerminal
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers

theorem returned (a : LIB_VTerminal.Args) (env : RSL.Env) (q : QM31)
 (called : LIB_VLib.terminalQm31Value a env = .ok q) :
 FIq_Terminal.terminal a.1 (claimsRaw a.2.1) (alphaRaw a.2.2.1)
  (challengesRaw a.2.2.2) = .ok (.Ok (LIB_VScalarCarriers.toRaw q)) := by
 have hm := NNV_ResultOkPort.value (LIB_VTerminal.model a) () q called
 have domain : LIB_VTerminal.Domain a := by
  unfold LIB_VTerminal.model at hm
  split at hm
  · assumption
  · cases hm
 have exact_ := LIB_VTerminal.model_exact a domain
 rw [hm,bind_tc_ok] at exact_
 obtain ⟨reply,run,image⟩ := NNV_ResultOkPort.mapped _ _ _ exact_.symm
 cases reply with
 | Err e => cases image
 | Ok raw =>
  have same := Except.ok.inj image
  subst raw
  unfold FIq_Terminal.terminal
  change (do let out ← LIB_VTerminal.native a
             match out with
             | .Ok x => .ok (.Ok (FIq_Carriers.fromQ x))
             | .Err e => .ok (.Err (FIq_Terminal.fromError e))) = _
  rw [run,bind_tc_ok]
  rfl
#print axioms returned
end AspisR1.NNV_FinishTerminal
end
