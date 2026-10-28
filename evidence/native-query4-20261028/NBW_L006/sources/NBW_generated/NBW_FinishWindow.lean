import NBW_Window
set_option autoImplicit false
noncomputable section
namespace NBW_FinishWindow
open Aeneas Aeneas.Std Result
open S8Kani2MutableExtraction.batched_weights
open S8Kani2MutableValue
/-- Exact association of the installed prefix writer to the KMX value law.
The original-value premise is only a read of the retained initial slice at
this same index; allocation/ownership remains a native caller obligation. -/
theorem prefix_index (f original : Nat → F.Q) (old : FinishSlice)
 (n : Nat) (i : Usize) (extent : n≤old.len.val) (bound : i.val<old.len.val)
 (read : Slice.index_usize old i=ok (original i.val)) :
 Slice.index_usize (prefixWrite f 0 n old) i=
   ok (KMX_CopyMeaning.loop f original 0 n i.val) := by
 by_cases inside : i.val<n
 · rw [S8Kani2PrefixWriteIndex.prefixWrite_index f n old i extent inside,
     KMX_CopyMeaning.copy_prefix,if_pos inside]
 · rw [S8Kani2PrefixWriteIndex.suffix_index_unchanged f n old i extent (by omega) bound,
     read,KMX_CopyMeaning.copy_prefix,if_neg inside]
/-- SAME self and initial destination. Reuse the existing finish induction;
its pointwise value is exactly the KMX full-window law. No native equality
is claimed here, and no successful finish is supplied as a hypothesis. -/
theorem finish_value (self : F.BW) (old : FinishSlice)
 (lengths : old.val.length≤self.raw.length) (before : Nat → F.Q) :
 ∃ out : FinishSlice, BatchedWeights.finish self old=ok out ∧
   ∀ i : Usize, i.val<old.len.val →
     Slice.index_usize out i=
       ok (KMX_CopyMeaning.loop (valueAt self) before 0 old.len.val i.val) := by
 obtain ⟨out,run,_,values⟩ := S8Kani2FinishCertificate.mutable_finish_total self old lengths
 refine ⟨out,run,?_⟩
 intro i hi
 rw [KMX_CopyMeaning.copy_prefix,if_pos hi]
 exact (values i hi).1
#print axioms prefix_index
#print axioms finish_value
end NBW_FinishWindow
end
