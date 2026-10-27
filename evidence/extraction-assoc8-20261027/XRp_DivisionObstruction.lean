import XRp_IndexedTrace
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRp_DivisionObstruction
open XRp_DivisionWitness XRp_IndexedWitness XRp_IndexedTrace

def emittedState (i : Usize) : Result (U32 × Array U32 8#usize) := do
  let (digit,c,restore) ← callback rank i
  ok (digit,restore c)
def indexedState : Result (U32 × Array U32 8#usize) := do
  let (q,digit) ← AspisR1Post25Sampler.sampler.qm31_div_pass rank
  ok (digit,q)

theorem ranks_differ : rank ≠ quotient := by
  intro h
  have hv := congrArg (fun a : Array U32 8#usize => a.val.head?) h
  change some 2147483647#u32 = some 1#u32 at hv
  have hx := congrArg UScalar.val (Option.some.inj hv)
  norm_num at hx

theorem division_commutation_false (i : Usize) : emittedState i ≠ indexedState := by
  unfold emittedState indexedState
  rw [emitted i,indexed]
  change ok (0#u32,rank) ≠ (ok (0#u32,quotient) : Result (U32 × Array U32 8#usize))
  intro h
  exact ranks_differ (congrArg Prod.snd (Result.ok.inj h))

theorem nonvacuity (i : Usize) :
    emittedState i = ok (0#u32,rank) ∧ indexedState = ok (0#u32,quotient) := by
  constructor
  · unfold emittedState; rw [emitted i]; rfl
  · unfold indexedState; rw [indexed]; rfl

#print axioms ranks_differ
#print axioms division_commutation_false
#print axioms nonvacuity
end XRp_DivisionObstruction
