import CostedAllocationLedgerM10

/-! Executable counters and a source allocation adequacy theorem are distinct.
The original HeapMirror interface cannot distinguish any of these annotations
by returned value; its zero ledger is provable. These are counterexamples to
inferring source allocation adequacy from that interface, not counterexamples
to the existence of a properly instrumented allocator. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.AllocationAdequacyObstructionM10
open CostedAllocationLedgerM10
open RawRecordedEagerExtractorReadsBin (RunView Coins)

/-- Diagnostic only. This must never be advertised as the source heap. -/
def zero : HeapMirror := ⟨fun _ _ => 0⟩

def overBound : HeapMirror :=
  ⟨fun run _ => (footprint*workConstant)*(run.1.length+1)+1⟩

theorem zero_satisfies (Q : Nat) : AllocationBound zero Q :=
  fun _ _ _ _ => Nat.zero_le _

theorem value_independent (h k : HeapMirror) (run : RunView) (coins : Coins) :
    (eval h run coins).1 = (eval k run coins).1 :=
  (value h run coins).trans (value k run coins).symm

theorem zero_ledger (Q : Nat) :
    RawExtractorCostComposedBin.LedgerRefinement (extractor zero) (params Q) Q :=
  ledger zero Q (zero_satisfies Q)

theorem overBound_rejected (Q : Nat) (run : RunView) (coins : Coins)
    (ha : run.2.2 = true) (hl : run.1.length ≤ Q+1161) :
    ¬ AllocationBound overBound Q := by
  intro h
  have hh := h run coins ha hl
  change (footprint*workConstant)*(run.1.length+1)+1 ≤
    (footprint*workConstant)*(run.1.length+1) at hh
  omega

/-- Even a genuinely nonzero stored-cell count cannot be justified by the
zero diagnostic annotation, although its Resource ledger is accepted. -/
theorem zero_misses_positive (run : RunView) (coins : Coins) (cells : Nat) (h : 0 < cells) :
    ¬ cells ≤ zero.bits run coins := by
  change ¬ cells ≤ 0
  omega

#print axioms zero_satisfies
#print axioms value_independent
#print axioms zero_ledger
#print axioms overBound_rejected
#print axioms zero_misses_positive
end AspisR1.AllocationAdequacyObstructionM10
end
