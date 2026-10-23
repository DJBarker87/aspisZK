import R1Z.ProverCommitEncoderGenericEval54
import R1Z.ProverCommitEncoderPhi53
import R1Z.ProverCommitArray49
/-! Generic source inverse transform with explicit local arithmetic semantics. -/
set_option autoImplicit false
namespace R1Z.ProverCommitEncoderGenericPhi54
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitArray49 ProverCommitEncoderGenericEval54
attribute [local irreducible] array
theorem exact_result {E K : Type} [CommRing K] (inst : scalar.CodeField E)
    (valid : E → Prop) (decode : E → K) (nv : U32 → K) (ops : Arithmetic inst valid decode nv)
    (sub_success : ∀ x y, valid x → valid y → ∃ z, inst.sub x y=ok z ∧ valid z ∧ decode z=decode x-decode y)
    (x y : E) (hx : valid x) (hy : valid y)
    (h : Nat → E) (hh : ∀ i, i<4 → valid (h i)) :
    ∃ out : Nat → E,
      generic54.phi_inverse inst (x) (y) (array 4#usize h)=
        ok (array 4#usize out) ∧
      (∀ i, i<4 → valid (out i)) ∧
      ∀ i : Fin 4, decode (out i.val)=ProverCommitEncoderPhi53.phi (decode x) (decode y) (fun i => decode (h i.val)) i := by
  obtain ⟨a,ha,hca,hda⟩ := ops.mul_success (y) (h 1) (hy) (hh 1 (by decide))
  obtain ⟨b,hb,hcb,hdb⟩ := ops.mul_success (x) (h 2) (hx) (hh 2 (by decide))
  obtain ⟨xy,hxy,hcxy,hdxy⟩ := ops.mul_success (x) (y) (hx) (hy)
  obtain ⟨c,hc,hcc,hdc⟩ := ops.mul_success (xy) (h 3) (hcxy) (hh 3 (by decide))
  obtain ⟨t0,ht0,hct0,hdt0⟩ := ops.add_success (h 0) (a) (hh 0 (by decide)) (hca)
  obtain ⟨t1,ht1,hct1,hdt1⟩ := ops.add_success (t0) (b) (hct0) (hcb)
  obtain ⟨o0,ho0,hco0,hdo0⟩ := ops.add_success (t1) (c) (hct1) (hcc)
  obtain ⟨t2,ht2,hct2,hdt2⟩ := sub_success (h 0) (a) (hh 0 (by decide)) (hca)
  obtain ⟨t3,ht3,hct3,hdt3⟩ := ops.add_success (t2) (b) (hct2) (hcb)
  obtain ⟨o1,ho1,hco1,hdo1⟩ := sub_success (t3) (c) (hct3) (hcc)
  obtain ⟨t4,ht4,hct4,hdt4⟩ := sub_success (t2) (b) (hct2) (hcb)
  obtain ⟨o2,ho2,hco2,hdo2⟩ := ops.add_success (t4) (c) (hct4) (hcc)
  obtain ⟨t5,ht5,hct5,hdt5⟩ := sub_success (t0) (b) (hct0) (hcb)
  obtain ⟨o3,ho3,hco3,hdo3⟩ := sub_success (t5) (c) (hct5) (hcc)
  let out : Nat → E := fun i => match i with | 0 => o0 | 1 => o1 | 2 => o2 | _ => o3
  refine ⟨out,?_,?_,?_⟩
  · simp only [generic54.phi_inverse,index 4#usize h 0#usize (by decide),
      index 4#usize h 1#usize (by decide),index 4#usize h 2#usize (by decide),
      index 4#usize h 3#usize (by decide),
      show (0#usize).val=0 from rfl,show (1#usize).val=1 from rfl,
      show (2#usize).val=2 from rfl,show (3#usize).val=3 from rfl,ha,hb,hxy,hc,ht0,ht1,ho0,ht2,ht3,ho1,ht4,ho2,ht5,ho3,bind_tc_ok]
    unfold array
    rfl
  · intro i hi
    interval_cases i
    · exact hco0
    · exact hco1
    · exact hco2
    · exact hco3
  · intro i
    fin_cases i
    · change decode o0=ProverCommitEncoderPhi53.phi (decode x) (decode y) (fun j => decode (h j.val)) 0
      rw [ProverCommitEncoderPhi53.phi_0]
      change decode o0=decode (h 0)+decode y*decode (h 1)+decode x*decode (h 2)+decode x*decode y*decode (h 3)
      rw [hdo0,hdt1,hdt0,hda,hdb,hdc,hdxy]
    · change decode o1=ProverCommitEncoderPhi53.phi (decode x) (decode y) (fun j => decode (h j.val)) 1
      rw [ProverCommitEncoderPhi53.phi_1]
      change decode o1=decode (h 0)-decode y*decode (h 1)+decode x*decode (h 2)-decode x*decode y*decode (h 3)
      rw [hdo1,hdt3,hdt2,hda,hdb,hdc,hdxy]
    · change decode o2=ProverCommitEncoderPhi53.phi (decode x) (decode y) (fun j => decode (h j.val)) 2
      rw [ProverCommitEncoderPhi53.phi_2]
      change decode o2=decode (h 0)-decode y*decode (h 1)-decode x*decode (h 2)+decode x*decode y*decode (h 3)
      rw [hdo2,hdt4,hdt2,hda,hdb,hdc,hdxy]
    · change decode o3=ProverCommitEncoderPhi53.phi (decode x) (decode y) (fun j => decode (h j.val)) 3
      rw [ProverCommitEncoderPhi53.phi_3]
      change decode o3=decode (h 0)+decode y*decode (h 1)-decode x*decode (h 2)-decode x*decode y*decode (h 3)
      rw [hdo3,hdt5,hdt0,hda,hdb,hdc,hdxy]

#print axioms exact_result
end R1Z.ProverCommitEncoderGenericPhi54
