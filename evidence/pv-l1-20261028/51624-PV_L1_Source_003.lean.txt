import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_003
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (queries : Array Std.U32 22#usize)
  (folded_word : Slice aspis_core.field.wide_exact.WideExact)
  (folded_salts : host_commitment.PrivateSalts) :
  Logged (alloc.vec.Vec Std.U8)
  := do
  let _ ← observe .publication 0 (ok ())
  prover.append_query_openings_loop out cc1 cc2 queries folded_word
    folded_salts 0#usize

theorem complete_result
  (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (queries : Array Std.U32 22#usize)
  (folded_word : Slice aspis_core.field.wide_exact.WideExact)
  (folded_salts : host_commitment.PrivateSalts) :
  erase (produce out cc1 cc2 queries folded_word folded_salts) = prover.append_query_openings out cc1 cc2 queries folded_word folded_salts := by
  unfold produce prover.append_query_openings
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
#print axioms complete_result
end PV_L1_Source_003
