import R1Z.PV_RunJoin_CheckColumnsLength66
import R1Z.PV_RunJoin_BackendBuildTrace60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BuildColumnDomain66
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_BackendMRows58 (Columns column)
variable [ExternalTypes] [ExternalFuns]
abbrev Q := aspis_core.field.QM31

theorem semantic (columns : Columns) (d g : Array Q 1024#usize)
    (success : host_semantic.check_semantic_columns columns d g=ok (.Ok ())) :
    ∀ l,l<26 → (column columns l).length=1024 := by
  unfold host_semantic.check_semantic_columns at success
  obtain ⟨status,hstatus,success⟩ := PV_RunJoin_ResultPost.bind_eq_ok success
  cases status with
  | Err e => cases success
  | Ok unit =>
    cases unit
    exact PV_RunJoin_CheckColumnsLength66.complete columns hstatus

/-- A successful builder has actually passed its row validator. No assumption
about the eventual semantic columns or backend matrix is introduced. -/
theorem helper {H T1 T2 : Type} (D : aspis_core.digest.Digest32 H)
    (helperInst : core.ops.function.FnOnce T1 (Q × Q) (core.result.Result (alloc.vec.Vec Q) r1_wire.Error))
    (commitInst : host_semantic.Commitments T2)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (columns : Columns) (d g padding : Array Q 1024#usize) (worker : T1)
    (initial next : T2) (hash : H) (variant : transport.Variant) (built : host_semantic.BuiltSemantics H)
    (success : host_semantic.build_with_helper_mode D helperInst commitInst public1 columns d g padding
      worker initial hash variant=ok (.Ok built,next)) :
    ∀ l,l<26 → (column columns l).length=1024 := by
  unfold host_semantic.build_with_helper_mode at success
  obtain ⟨status,hstatus,success⟩ := PV_RunJoin_ResultPost.bind_eq_ok success
  cases status with
  | Err e => cases success
  | Ok unit =>
    cases unit
    exact semantic columns d g hstatus

#print axioms semantic
#print axioms helper
end R1Z.PV_RunJoin_BuildColumnDomain66
