import R1Z.PV_RunJoin_LiftPayload63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LiftValue63
open Aeneas Aeneas.Std ProverRwFull ProverCommitNativeOps47
open PV_RunJoin_LiftPayload63
abbrev W := aspis_core.field.wide_exact.WideExact

def value (q : aspis_core.field.QM31) : W :=
  ProverRwDictionaryTower.fromW (embedded (normalize (PV_RunJoin_SemanticScalar50.raw q)))

theorem cell (m : U32) : value (PV_RunJoin_LiftCell63.lifted m)=PV_RunJoin_BackendMInput58.value m := by
  unfold value PV_RunJoin_BackendMInput58.value
  rw [PV_RunJoin_LiftCell63.normalized]

def widePayload (column : alloc.vec.Vec aspis_core.field.M31) (row : Nat) : Nat → List W
  | 0 => []
  | n+1 => PV_RunJoin_BackendMInput58.value (entry column row)::widePayload column (row+1) n

theorem map_payload (column : alloc.vec.Vec aspis_core.field.M31) (row n : Nat) :
    (payload column row n).map value=widePayload column row n := by
  induction n generalizing row with
  | zero => rfl
  | succ n ih => simp only [payload,List.map_cons,cell,widePayload,ih]

#print axioms value
#print axioms cell
#print axioms widePayload
#print axioms map_payload
end R1Z.PV_RunJoin_LiftValue63
