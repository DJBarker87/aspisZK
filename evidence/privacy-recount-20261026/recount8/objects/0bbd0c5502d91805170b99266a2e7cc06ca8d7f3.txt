import R1Z.ProverCommitSubtraction47
/-! Canonical non-embedded QM31 arithmetic needed by full WideExact output
fields. Raw mul-by-r is kept separate from its decoded value theorem. -/
set_option autoImplicit false
namespace R1Z.ProverCommitQOps48
open Aeneas Aeneas.Std Result ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact

theorem add (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.Q, AspisR1ProducerChecked47.field.QM31.add (fromQ x) (fromQ y)=ok (fromQ z) ∧
      Canonical z ∧ decode z=decode x+decode y := by
  obtain ⟨z,hz,hc,hd⟩ := current_qm_add_exact x y hx hy
  refine ⟨z,?_,hc,hd⟩
  rw [addQ,hz]
  rfl

theorem mul (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.Q, AspisR1ProducerChecked47.field.QM31.mul (fromQ x) (fromQ y)=ok (fromQ z) ∧
      Canonical z ∧ decode z=decode x*decode y := by
  obtain ⟨z,hz,hc,hd⟩ := current_qm_mul_exact x y hx hy
  refine ⟨z,?_,hc,hd⟩
  rw [mulQ,hz]
  rfl

theorem r_raw (x : Old.C) (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM x) :
    ∃ z : Old.C, AspisR1ProducerChecked47.field.mul_by_r (fromC x)=ok (fromC z) ∧
      AspisR1.ExtractedCurrentTowerAdd.CanonicalCM z ∧
      z.a.val=(((x.a.val+x.a.val)%2147483647)+2147483647-x.b.val)%2147483647 ∧
      z.b.val=(x.a.val+(x.b.val+x.b.val)%2147483647)%2147483647 := by
  obtain ⟨a2,ea2,va2,ca2⟩ := AspisR1.ExtractedCurrentM31AddSub.current_add_mod x.a x.a hx.1 hx.1
  obtain ⟨a,ea,va,ca⟩ := AspisR1.ExtractedCurrentM31AddSub.current_sub_mod a2 x.b ca2 hx.2
  obtain ⟨b2,eb2,vb2,cb2⟩ := AspisR1.ExtractedCurrentM31AddSub.current_add_mod x.b x.b hx.2 hx.2
  obtain ⟨b,eb,vb,cb⟩ := AspisR1.ExtractedCurrentM31AddSub.current_add_mod x.a b2 hx.1 cb2
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,?_,?_⟩
  · rw [rC]
    simp only [AspisR1Qm31ArithmeticProbe.field.mul_by_r,
      AspisR1Qm31ArithmeticProbe.field.M31.double,ea2,ea,eb2,eb,bind_tc_ok,mapR]
  · simpa only [va2] using va
  · simpa only [vb2] using vb

#print axioms add
#print axioms mul
#print axioms r_raw
end R1Z.ProverCommitQOps48
