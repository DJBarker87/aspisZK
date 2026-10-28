import R1Z.ProverCommitMulU48
import R1Z.ProverCommitM31Ops48
/-! Canonical CM31 operations of the current release extraction, as prerequisites
for the native semantic inverse and power kernels. -/
set_option autoImplicit false
namespace R1Z.ProverCommitNativeC49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47
open AspisV8R15.ExactTowerBase
abbrev Canonical := AspisR1.ExtractedCurrentTowerAdd.CanonicalCM
abbrev value := ProverCommitMulU48.decodeC

def source (x : Old.C) : field.CM31 := ProverCommitRelease47.convC (fromC x)

theorem add (x y : Old.C) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.C, field.CM31.add (source x) (source y)=ok (source z) ∧
      Canonical z ∧ value z=value x+value y := by
  obtain ⟨a,ha,hca,hda⟩ := ProverCommitM31Ops48.add_exact x.a y.a hx.1 hy.1
  obtain ⟨b,hb,hcb,hdb⟩ := ProverCommitM31Ops48.add_exact x.b y.b hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,⟨hca,hcb⟩,?_⟩
  · simp only [field.CM31.add,source,ProverCommitRelease47.convC,fromC,ha,hb,bind_tc_ok]
  · apply QuadraticAlgebra.ext
    · exact hda
    · exact hdb

theorem sub (x y : Old.C) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.C, field.CM31.sub (source x) (source y)=ok (source z) ∧
      Canonical z ∧ value z=value x-value y := by
  obtain ⟨a,ha,hca,hda⟩ := ProverCommitM31Ops48.sub_exact x.a y.a hx.1 hy.1
  obtain ⟨b,hb,hcb,hdb⟩ := ProverCommitM31Ops48.sub_exact x.b y.b hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,⟨hca,hcb⟩,?_⟩
  · simp only [field.CM31.sub,source,ProverCommitRelease47.convC,fromC,ha,hb,bind_tc_ok]
  · apply QuadraticAlgebra.ext
    · exact hda
    · exact hdb

theorem embedC_mul (x y : AspisV8R17.QM31WordResidues.C) :
    AspisV8R17.QM31WordTower.embedC (AspisV8R17.QM31WordResidues.cMul x y)=
      AspisV8R17.QM31WordTower.embedC x*AspisV8R17.QM31WordTower.embedC y := by
  apply QuadraticAlgebra.ext <;>
    simp [AspisV8R17.QM31WordTower.embedC,AspisV8R17.QM31WordResidues.cMul] <;> ring

theorem mul (x y : Old.C) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.C, field.CM31.mul (source x) (source y)=ok (source z) ∧
      Canonical z ∧ value z=value x*value y := by
  obtain ⟨z,hz,hc,hr,hi⟩ := AspisR1.ExtractedCurrentCM31Mul.current_mul_words x y hx hy
  have checked : AspisR1ProducerChecked47.field.CM31.mul (fromC x) (fromC y)=ok (fromC z) := by
    rw [ProverCommitPrimitive47.mulC,hz];rfl
  refine ⟨z,ProverCommitRelease47.mulC _ _ _ checked,hc,?_⟩
  have hw : (z.a.val,z.b.val)=AspisV8R17.GeneratedQM31Products.mulWords (x.a.val,x.b.val) (y.a.val,y.b.val) :=
    Prod.ext hr hi
  change AspisV8R17.QM31WordTower.embedC (AspisV8R17.QM31WordResidues.decodeC (z.a.val,z.b.val))=_
  rw [hw,AspisV8R17.QM31WordResidues.decode_mul,embedC_mul]
  rfl

theorem mul_r (x : Old.C) (hx : Canonical x) :
    ∃ z : Old.C, field.mul_by_r (source x)=ok (source z) ∧ Canonical z ∧ value z=qm31R*value x := by
  obtain ⟨z,hz,hc,ha,hb⟩ := ProverCommitQOps48.r_raw x hx
  exact ⟨z,ProverCommitRelease47.rC _ _ hz,hc,ProverCommitMulU48.r_coordinates x z hx ha hb⟩

#print axioms add
#print axioms sub
#print axioms embedC_mul
#print axioms mul
#print axioms mul_r
end R1Z.ProverCommitNativeC49
