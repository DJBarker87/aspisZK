import R1Z.PV_CB_ProducerOffsetChoice
import R1Z.PV_CB_PartialArrayUpdate
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_ProducerOffsetControl
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_ProducerLimb
variable [ExternalTypes]
abbrev Source := aspis_statement.pool_v1.pair_trace.PoolV1PairTraceCellV1
abbrev Valid (limbs : Array Limb 16#usize) := PV_CB_CanonicalArrays.Valid OffsetValid limbs

/-- Owned control step using the checked primitive source equations. Its
    association with the private Rust tuple_cells body is still required. -/
def step (ops : ExternalFuns) (tweak : U32) (adjust : Usize → Bool)
    (source : Usize → Source) (i : Usize) (limbs : Array Limb 16#usize) : Result (Array Limb 16#usize) := do
  let value ← PV_CB_ProducerOffsetChoice.offset ops (adjust i) tweak
  Array.update limbs i (.Cell (source i) value)

theorem step_valid (ops : ExternalFuns) (tweak : U32) (vt : PV_CB_CanonicalM31.Valid tweak)
    (adjust : Usize → Bool) (source : Usize → Source) (i : Usize)
    (limbs : Array Limb 16#usize) (vl : Valid limbs) :
    PV_CB_PartialForward.Post Valid (step ops tweak adjust source i limbs) := by
  obtain ⟨value,hvalue,vvalue⟩ := PV_CB_ProducerOffsetChoice.canonical ops (adjust i) tweak vt
  simp only [step,hvalue,bind_tc_ok]
  exact PV_CB_PartialArrayUpdate.update OffsetValid limbs vl i (.Cell (source i) value) vvalue

theorem finite (ops : ExternalFuns) (tweak : U32) (vt : PV_CB_CanonicalM31.Valid tweak)
    (adjust : Usize → Bool) (source : Usize → Source) (fuel : Nat) (i : Usize)
    (limbs : Array Limb 16#usize) (vl : Valid limbs) :
    PV_CB_PartialForward.Post Valid
      (PV_CB_ForwardLoop.finite (step ops tweak adjust source) fuel i limbs) :=
  PV_CB_PartialForward.finite Valid (step ops tweak adjust source)
    (fun i state valid => step_valid ops tweak vt adjust source i state valid) fuel i limbs vl

theorem run (ops : ExternalFuns) (tweak : U32) (vt : PV_CB_CanonicalM31.Valid tweak)
    (adjust : Usize → Bool) (source : Usize → Source) (stop : Usize) :
    PV_CB_PartialForward.Post Valid
      (PV_CB_ForwardLoop.run (step ops tweak adjust source) 0#usize stop
        (Array.repeat 16#usize aspis_statement.pool_v1.pair_trace.PoolV1PairTupleLimbV1.Zero)) := by
  rw [PV_CB_ForwardLoop.source (step ops tweak adjust source) stop.val 0#usize stop _ (by simp)]
  exact finite ops tweak vt adjust source stop.val 0#usize _ PV_CB_ProducerOffsetChoice.empty_valid
#print axioms step_valid
#print axioms finite
#print axioms run
end R1Z.PV_CB_ProducerOffsetControl
