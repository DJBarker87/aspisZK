import AspisR1ProducerRelease47.EncoderLeaves54
import R1Z.ProverCommitEncoderExact54
/-! All four folded-leaf evaluations at the actual consecutive domain indices. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitFoldedValues54
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48

theorem four_val (v : Usize) (hv : v.val<65536) :
    (Usize.wrapping_mul 4#usize v).val=4*v.val := by
  rw [Usize.wrapping_mul_val_eq,show (4#usize).val=4 from rfl]
  apply Nat.mod_eq_of_lt
  have hs := ProverCommitEncoderReverse54.size_large
  change 262144<UScalar.size .Usize at hs
  omega

theorem offset_val (v : Usize) (hv : v.val<65536) (s : Usize) (hs : s.val<4) :
    (Usize.wrapping_add (Usize.wrapping_mul 4#usize v) s).val=4*v.val+s.val := by
  rw [Usize.wrapping_add_val_eq,four_val v hv]
  apply Nat.mod_eq_of_lt
  have hb := ProverCommitEncoderReverse54.size_large
  change 262144<UScalar.size .Usize at hb
  omega

attribute [local irreducible] source value sourceArray

theorem exact_result (f : Nat → Raw) (hf : ∀ i, i<256 → canonical (f i))
    (v : Usize) (u : Fin 65536) (hv : v.val=u.val) :
    ∃ out : Nat → Raw, leaves54.folded_values (sourceArray 256#usize f) v=ok (sourceArray 4#usize out) ∧
      (∀ s, s<4 → canonical (out s)) ∧
      ∀ s : Fin 4, value (out s.val)=AspisWide.FinalEncoder.exactFinalEncoder
        (fun i => value (f i.val)) (AspisV5ComponentCConcreteFoldLinearity.childIndex u s) := by
  have hvbound : v.val<65536 := by rw [hv];exact u.isLt
  let j := Usize.wrapping_mul 4#usize v
  obtain ⟨a,ha,hca,hda⟩ := ProverCommitEncoderExact54.eval_at_result f hf j
    (AspisV5ComponentCConcreteFoldLinearity.childIndex u 0) (by rw [four_val v hvbound,hv];rfl)
  obtain ⟨b,hb,hcb,hdb⟩ := ProverCommitEncoderExact54.eval_at_result f hf (Usize.wrapping_add j 1#usize)
    (AspisV5ComponentCConcreteFoldLinearity.childIndex u 1) (by rw [offset_val v hvbound _ (by decide),hv];rfl)
  obtain ⟨c,hc,hcc,hdc⟩ := ProverCommitEncoderExact54.eval_at_result f hf (Usize.wrapping_add j 2#usize)
    (AspisV5ComponentCConcreteFoldLinearity.childIndex u 2) (by rw [offset_val v hvbound _ (by decide),hv];rfl)
  obtain ⟨d,hd,hcd,hdd⟩ := ProverCommitEncoderExact54.eval_at_result f hf (Usize.wrapping_add j 3#usize)
    (AspisV5ComponentCConcreteFoldLinearity.childIndex u 3) (by rw [offset_val v hvbound _ (by decide),hv];rfl)
  dsimp only [j] at ha hb hc hd
  let out : Nat → Raw := fun i => match i with | 0 => a | 1 => b | 2 => c | _ => d
  refine ⟨out,?_,?_,?_⟩
  · simp only [leaves54.folded_values,lift,bind_tc_ok,ha,hb,hc,hd]
    unfold sourceArray
    rfl
  · intro s hs
    interval_cases s
    · exact hca
    · exact hcb
    · exact hcc
    · exact hcd
  · intro s
    fin_cases s
    · exact hda
    · exact hdb
    · exact hdc
    · exact hdd

#print axioms four_val
#print axioms offset_val
#print axioms exact_result
end R1Z.ProverCommitFoldedValues54
