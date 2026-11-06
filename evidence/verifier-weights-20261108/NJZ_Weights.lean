import NJR_ReservationRaw
import NJR_FlushComposition
import NJJ_Pending
import NJJ_Value
set_option autoImplicit false
noncomputable section
namespace NJZ_Weights
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
abbrev Row := Port3_NativePendingBody.Row

/-- Forward (aq)(5) instantiation of the actual filled source occurrence and
one-row native initialization cuts. Reservation is universally quantified data
at that occurrence; both reserve arms remain. No allocation success premise. -/
theorem new_source (reservation : NP6_StdModel.Reservation)
 (weights : Slice aspis_core.field.QM31) (size : weights.val.length=64)
 (states : Nat → alloc.vec.Vec Row)
 (cuts : NJC_FilledClause.reserved reservation=true → ∀ i, i<64 →
  NJJ_Cuts.pendingStep weights (states i) (states (i+1)) i (i+1)) :
 Port3_QueryInstall.result
   (Port3_NativePendingBody.extracted (NJR_ReservationRaw.filled reservation) weights)=
 if NJC_FilledClause.reserved reservation then
  ok (.Ok (⟨states 64,0#usize⟩ : verifier.BatchedWeights)) else ok (.Err .Allocation) := by
 rw [NJR_ReservationRaw.pending]
 exact NJJ_Pending.source (NJC_FilledClause.reserved reservation) weights size states cuts

/-- One row, every U64 input, exact reduction. The native singleton projection
is independent of every unselected row and terms, as NJJ_Value.projection proves. -/
theorem value_source (b : S8Kani2MutableValue.F.BW) (i : Usize)
 (bound : i.val<b.raw.length) :
 ∃ row : S8OwnedP6ValueModel.Row, b.raw.val[i.val]?=some row ∧
 S8Kani2MutableValue.F.value b i=ok
  (S8Kani2FinishReferenceJoin.toFinish (S8OwnedP6Finish.modelValue row)) :=
 NJJ_Value.source b i bound

/-- Every full mutable store/frame cut is instantiated with the value model
on the SAME raw index; finite induction identifies all64 destination cells.
The immutable receiver clauses remain explicit in each cut. -/
theorem finish_source (b : VTop_Stages.verifier.BatchedWeights)
 (old : Slice VTop_Stages.aspis_core.field.QM31)
 (rawSize : b.raw.val.length=64) (oldSize : old.val.length=64)
 (states : Nat → List VTop_Stages.aspis_core.field.QM31)
 (initial : states 0=old.val)
 (cuts : ∀ i,i<64→∃ row, b.raw.val[i]?=some row ∧
  NJR_Cuts.flushStep b.raw.val b.raw.val b.terms b.terms
   (states i) (states (i+1)) i (NJJ_Flush.cell row)) :
 Port3_FlushInstall.flush b old=ok (NJJ_Flush.output b) ∧
 states 64=(NJJ_Flush.output b).val ∧
 (∀ q∈states 64,Port3_FlushInstall.Canonical q) := by
 have sizes : ∀ n,n≤64→(states n).length=64 := by
  intro n
  induction n with
  | zero => intro _;rw [initial];exact oldSize
  | succ n ih =>
    intro hn
    obtain ⟨row,read,cut⟩:=cuts n (by omega)
    rw [cut.2.2.1]
    exact ih (by omega)
 apply NJR_FlushComposition.source b old rawSize oldSize states sizes
 intro i hi j hj
 obtain ⟨row,read,cut⟩ := cuts i hi
 rw [cut.2.2.2 j (by rw [sizes i (by omega)];exact hj),read]
 rfl

#print axioms new_source
#print axioms value_source
#print axioms finish_source
end NJZ_Weights
