import RPu_FJf_PartialValue
import RPv_FJd_ReferenceDot
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_PartialReference
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ NE)
open scoped BigOperators

theorem sumPrefix (f : Slice U8) (common : Array NQ 16#usize) (s : Usize) (n : Nat) :
    FJf_PartialCell.sumPrefix f common s n=
      ∑ j ∈ Finset.range n,FJf_PartialCell.term f common s j := by
  induction n with
  | zero => simp only [FJf_PartialCell.sumPrefix,Finset.range_zero,Finset.sum_empty]
  | succ n ih => rw [FJf_PartialCell.sumPrefix,Finset.sum_range_succ,ih]

theorem value (f : Slice U8) (common : Array NQ 16#usize) (s : Usize)
    (hs : s.val < 4) (hc : FJf_QMArray.canon common) (out : NE)
    (run : FIo_Native.weights.partial_dot f common s=ok (.Ok out)) :
    FIo_WideValues.Canon out ∧ AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide out)=
      ∑ j ∈ Finset.range 16,FJf_PartialCell.term f common s j := by
  have h := FJf_PartialValue.sixteen f common s hs hc out run
  exact ⟨h.1,h.2.trans (sumPrefix f common s 16)⟩
#print axioms sumPrefix
#print axioms value
end AspisR1.FJf_PartialReference
end
