import R1Z.ProverCommitLinearLoop50
import R1Z.ProverCommitScale50
import R1Z.ProverCommitNativeQSquare49
/-! Current optimized selected-mask forms and fixed exponentiation chain. -/
set_option autoImplicit false
namespace R1Z.ProverCommitLinear50
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
section Algebra
variable {K : Type} [Field K]

theorem form0 (p : Nat → K) :
    ProverCommitLinearMath50.sum p 10*3+ProverCommitLinearMath50.weighted p 10*22=
      R0P.Mask.maskLinear 0 (fun i : Fin 10 => p i.val) := by
  have h := ProverCommitLinearMath50.form p 0
  simp only [Nat.cast_zero,mul_zero,add_zero] at h
  rw [←h];ring

theorem form16 (p : Nat → K) :
    ProverCommitLinearMath50.sum p 10*275+ProverCommitLinearMath50.weighted p 10*150=
      R0P.Mask.maskLinear 16 (fun i : Fin 10 => p i.val) := by
  rw [←ProverCommitLinearMath50.form p 16]
  push_cast
  ring

theorem chain (x : K) : (x^16*x^8)*x^2=x^26 := by ring
end Algebra

theorem forms (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i)) :
    ∃ a b : Old.Q, linear50.eval (ProverCommitQArray48.array 10#usize p)=
      ok (ProverCommitNativeQ48.source a,ProverCommitNativeQ48.source b) ∧
      Canonical a ∧ Canonical b ∧
      decode a=R0P.Mask.maskLinear 0 (fun i : Fin 10 => decode (p i.val)) ∧
      decode b=R0P.Mask.maskLinear 16 (fun i : Fin 10 => decode (p i.val)) := by
  obtain ⟨s,w,hgo,hcs,hcw,hvalues⟩ := ProverCommitLinearLoop50.go p hp 10 10#u8 rfl (by decide)
    zero zero zero_canonical zero_canonical
  rw [ProverCommitLinearMath50.stats_value,zero_decode] at hvalues
  have hvs : decode s=ProverCommitLinearMath50.sum (fun i => decode (p i)) 10 := by
    simpa only [zero_add] using congrArg Prod.fst hvalues
  have hvw : decode w=ProverCommitLinearMath50.weighted (fun i => decode (p i)) 10 := by
    simpa only [mul_zero,zero_add] using congrArg Prod.snd hvalues
  obtain ⟨s3,hs3,hcs3,hvs3⟩ := ProverCommitScale50.scale s 3#u32
  obtain ⟨w22,hw22,hcw22,hvw22⟩ := ProverCommitScale50.scale w 22#u32
  obtain ⟨a,ha,hca,hva⟩ := ProverCommitNativeQ48.add s3 w22 hcs3 hcw22
  obtain ⟨s275,hs275,hcs275,hvs275⟩ := ProverCommitScale50.scale s 275#u32
  obtain ⟨w150,hw150,hcw150,hvw150⟩ := ProverCommitScale50.scale w 150#u32
  obtain ⟨b,hb,hcb,hvb⟩ := ProverCommitNativeQ48.add s275 w150 hcs275 hcw150
  refine ⟨a,b,?_,hca,hcb,?_,?_⟩
  · rw [linear50.eval,ProverCommitQArray48.source_zero,hgo]
    simp only [bind_tc_ok]
    change (do
      let q ← field.QM31.mul_m31 (ProverCommitNativeQ48.source s) 3#u32
      let q1 ← field.QM31.mul_m31 (ProverCommitNativeQ48.source w) 22#u32
      let q2 ← field.QM31.add q q1
      let q3 ← field.QM31.mul_m31 (ProverCommitNativeQ48.source s) 275#u32
      let q4 ← field.QM31.mul_m31 (ProverCommitNativeQ48.source w) 150#u32
      let q5 ← field.QM31.add q3 q4
      ok (q2,q5))=_
    rw [hs3];simp only [bind_tc_ok]
    rw [hw22];simp only [bind_tc_ok]
    rw [ha];simp only [bind_tc_ok]
    rw [hs275];simp only [bind_tc_ok]
    rw [hw150];simp only [bind_tc_ok]
    rw [hb];rfl
  · rw [hva,hvs3,hvw22,hvs,hvw]
    exact form0 _
  · rw [hvb,hvs275,hvw150,hvs,hvw]
    exact form16 _

theorem power26 (x : Old.Q) (hx : Canonical x) :
    ∃ z : Old.Q, linear50.power26 (ProverCommitNativeQ48.source x)=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=(decode x)^26 := by
  obtain ⟨x2,h2,hc2,hv2⟩ := ProverCommitNativeQSquare49.square x hx
  obtain ⟨x4,h4,hc4,hv4⟩ := ProverCommitNativeQSquare49.square x2 hc2
  obtain ⟨x8,h8,hc8,hv8⟩ := ProverCommitNativeQSquare49.square x4 hc4
  obtain ⟨x16,h16,hc16,hv16⟩ := ProverCommitNativeQSquare49.square x8 hc8
  obtain ⟨x24,h24,hc24,hv24⟩ := ProverCommitNativeQ48.mul x16 x8 hc16 hc8
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitNativeQ48.mul x24 x2 hc24 hc2
  have h2' : decode x2=(decode x)^2 := by rw [hv2,pow_two]
  have h4' : decode x4=(decode x)^4 := by rw [hv4,h2'];ring
  have h8' : decode x8=(decode x)^8 := by rw [hv8,h4'];ring
  have h16' : decode x16=(decode x)^16 := by rw [hv16,h8'];ring
  refine ⟨z,?_,hcz,?_⟩
  · simp only [linear50.power26,h2,h4,h8,h16,h24,hz,bind_tc_ok]
  · rw [hdz,hv24,h16',h8',h2']
    exact chain _

#print axioms form0
#print axioms form16
#print axioms chain
#print axioms forms
#print axioms power26
end R1Z.ProverCommitLinear50
