import R1Z.ProverCommitQOps48
/-! Exact value of the full (nonzero high-coordinate) wide multiplication
constant. No sparse-input or zero-product premise is used. -/
set_option autoImplicit false
namespace R1Z.ProverCommitMulU48
open Aeneas Aeneas.Std Result ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)
open AspisV8R15.ExactTowerBase

def decodeC (x : Old.C) : CM31Exact := ⟨(x.a.val : M31Exact),(x.b.val : M31Exact)⟩

theorem r_coordinates (x z : Old.C) (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM x)
    (ha : z.a.val=(((x.a.val+x.a.val)%2147483647)+2147483647-x.b.val)%2147483647)
    (hb : z.b.val=(x.a.val+(x.b.val+x.b.val)%2147483647)%2147483647) :
    decodeC z=qm31R*decodeC x := by
  have hza : (z.a.val : M31Exact)=(x.a.val : M31Exact)+(x.a.val : M31Exact)-(x.b.val : M31Exact) := by
    rw [ha,ProverCommitSubDecode47.limb_sub _ _ hx.2,ZMod.natCast_mod,Nat.cast_add]
  have hzb : (z.b.val : M31Exact)=(x.a.val : M31Exact)+((x.b.val : M31Exact)+(x.b.val : M31Exact)) := by
    rw [hb,ZMod.natCast_mod,Nat.cast_add,ZMod.natCast_mod,Nat.cast_add]
  calc
    _ = AspisV8R17.QuadraticTowerOperations.cr (decodeC x) := by
      apply QuadraticAlgebra.ext
      · exact hza
      · exact hzb
    _ = _ := AspisV8R17.QuadraticTowerOperations.cr_eq _

theorem mul_u (x : Old.Q) (hx : Canonical x) :
    ∃ z : Old.Q, AspisR1ProducerChecked47.field.wide_exact.mul_u (fromQ x)=ok (fromQ z) ∧
      Canonical z ∧ decode z=decode x*AspisWideTower.wideU := by
  obtain ⟨r,hr,hcr,ha,hb⟩ := ProverCommitQOps48.r_raw x.c1 hx.2
  have hd := r_coordinates x.c1 r hx.2 ha hb
  refine ⟨⟨r,x.c0⟩,?_,⟨hcr,hx.1⟩,?_⟩
  · simp only [AspisR1ProducerChecked47.field.wide_exact.mul_u,fromQ,hr,bind_tc_ok]
  · apply QuadraticAlgebra.ext
    · simpa [decode,AspisWideTower.wideU,decodeC,mul_comm] using hd
    · simp [decode,AspisWideTower.wideU]

#print axioms r_coordinates
#print axioms mul_u
end R1Z.ProverCommitMulU48
