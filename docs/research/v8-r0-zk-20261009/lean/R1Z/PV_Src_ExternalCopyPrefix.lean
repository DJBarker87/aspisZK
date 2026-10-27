import R1Z.PV_Src_ExternalWritePrefix
import R1Z.PV_Src_ExternalCopyBlockStep

/-! The fixed-input copy overwrites the whole suffix. Its result depends on
an initial output array only through the already processed prefix. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ExternalCopyPrefix
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_Src_ExternalBlockStep

theorem loop (n : Nat) (s a b : State) (g : Usize) (count : g.val+n=4)
    (h : ∀ j, j < 4*g.val → a.val[j]! = b.val[j]!) :
    R0PoseidonCopy.ext_groups_loop s a g = R0PoseidonCopy.ext_groups_loop s b g := by
  induction n generalizing a b g with
  | zero =>
    have hab : a=b := by
      apply BuilderRecordCanonical.array_ext
      intro j hj
      exact h j (by simp only [UScalar.ofNatCore_val_eq] at hj;omega)
    rw [hab]
  | succ n ih =>
    have hg : g.val < 4 := by omega
    obtain ⟨m,hm,_,_,_,_⟩ := mat4_lift (K := ZMod 2147483647)
      s.val[(base g).val]!
      s.val[(Usize.wrapping_add (base g) 1#usize).val]!
      s.val[(Usize.wrapping_add (base g) 2#usize).val]!
      s.val[(Usize.wrapping_add (base g) 3#usize).val]!
      (fun i => liftU (K := ZMod 2147483647) s.val[4*g.val+i.val]!)
      (by rw [base_val g hg];rfl)
      (by rw [offset_val g hg _ (by decide)];rfl)
      (by rw [offset_val g hg _ (by decide)];rfl)
      (by rw [offset_val g hg _ (by decide)];rfl)
    rw [PV_Src_ExternalCopyBlockStep.source s a g hg m hm,
      PV_Src_ExternalCopyBlockStep.source s b g hg m hm]
    exact ih _ _ _ (by rw [BuilderRecordsArray.next_val g (by omega)];omega)
      (PV_Src_ExternalWritePrefix.extend a b g hg m h)

#print axioms loop
end R1Z.PV_Src_ExternalCopyPrefix
