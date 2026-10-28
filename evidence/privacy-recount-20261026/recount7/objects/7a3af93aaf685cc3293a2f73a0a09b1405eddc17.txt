import AspisR1ProducerRelease47.Basis
import R1Z.ProverCommitNativeOps47
import R1Z.ProverCommitSubRaw47
import R1Z.ProverCommitSubDecode47
/-! Exact source subtraction and Chebyshev doubling on canonical embedded
inputs. The primitive's checked-success intermediate is discharged here. -/
set_option autoImplicit false
namespace R1Z.ProverCommitSubtraction47
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47 ProverCommitRelease47
open AspisR1.ExtractedCurrentQM31Exact

def one : Old.Q := ⟨⟨1#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩

theorem one_canonical : Canonical one := ⟨⟨by decide,by decide⟩,⟨by decide,by decide⟩⟩
theorem one_decode : decode one=1 := rfl

theorem qsub_checked (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.Q,
      AspisR1ProducerChecked47.field.QM31.sub (fromQ x) (fromQ y)=ok (fromQ z) ∧
      Canonical z ∧ decode z=decode x-decode y := by
  obtain ⟨lo,hlo,hclo,ha,hb⟩ := AspisR1.ExtractedCurrentTowerAdd.current_cm_sub_mod x.c0 y.c0 hx.1 hy.1
  obtain ⟨hi,hhi,hchi,hc,hd⟩ := AspisR1.ExtractedCurrentTowerAdd.current_cm_sub_mod x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨lo,hi⟩,ProverCommitSubRaw47.raw x y lo hi hlo hhi,⟨hclo,hchi⟩,?_⟩
  exact ProverCommitSubDecode47.coordinates x y ⟨lo,hi⟩ hy ha hb hc hd

theorem sub_exact (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.Q,
      field.wide_exact.WideExact.sub (ProverCommitNativeOps47.embedded x)
        (ProverCommitNativeOps47.embedded y)=ok (ProverCommitNativeOps47.embedded z) ∧
      Canonical z ∧ decode z=decode x-decode y := by
  obtain ⟨z,hz,hcanon,hdecode⟩ := qsub_checked x y hx hy
  have low := ProverCommitRelease47.subQ _ _ _ hz
  have high := ProverCommitRelease47.subQ _ _ _
    (ProverCommitSubfieldOps47.sub_self zero zero_canonical)
  refine ⟨z,?_,hcanon,hdecode⟩
  unfold field.wide_exact.WideExact.sub ProverCommitNativeOps47.embedded
    ProverCommitSubfieldOps47.embedded convE
  rw [low,high]
  rfl

theorem source_one : field.wide_exact.WideExact.ONE=ProverCommitNativeOps47.embedded one := by
  rw [field.wide_exact.WideExact.ONE,field.QM31.ONE,field.QM31.ZERO]
  rfl

def double (x : field.wide_exact.WideExact) : Result field.wide_exact.WideExact := do
  let square ← field.wide_exact.WideExact.mul x x
  let twice ← field.wide_exact.WideExact.add square square
  field.wide_exact.WideExact.sub twice field.wide_exact.WideExact.ONE

theorem double_exact (x : Old.Q) (hx : Canonical x) :
    ∃ z : Old.Q, double (ProverCommitNativeOps47.embedded x)=ok (ProverCommitNativeOps47.embedded z) ∧
      Canonical z ∧ decode z=2*(decode x)^2-1 := by
  obtain ⟨sq,hsq,hcsq,hdsq⟩ := ProverCommitNativeOps47.mul_exact x x hx hx
  obtain ⟨tw,htw,hctw,hdtw⟩ := ProverCommitNativeOps47.add_exact sq sq hcsq hcsq
  obtain ⟨z,hz,hcz,hdz⟩ := sub_exact tw one hctw one_canonical
  refine ⟨z,?_,hcz,?_⟩
  · simp only [double,hsq,htw,source_one,hz,bind_tc_ok]
  · rw [hdz,hdtw,hdsq,one_decode]
    ring

#print axioms one_canonical
#print axioms one_decode
#print axioms qsub_checked
#print axioms sub_exact
#print axioms source_one
#print axioms double_exact
end R1Z.ProverCommitSubtraction47
