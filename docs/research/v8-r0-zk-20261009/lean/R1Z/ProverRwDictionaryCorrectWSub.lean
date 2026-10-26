import R1Z.ProverRwDictionaryScalar
import R1Z.ProverCommitWideOps48
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryCorrectWSub
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48
open AspisR1ProducerRelease47
variable [ExternalTypes]
theorem source_sub (x y : Raw) (hx : canonical x) (hy : canonical y) :
    ∃ z : Raw, field.wide_exact.WideExact.sub (source x) (source y)=ok (source z) ∧
      canonical z ∧ value z=value x-value y := by
  obtain ⟨lo,hlo,hclo,hdlo⟩ := ProverCommitSubtraction47.qsub_checked x.1 y.1 hx.1 hy.1
  obtain ⟨hi,hhi,hchi,hdhi⟩ := ProverCommitSubtraction47.qsub_checked x.2 y.2 hx.2 hy.2
  have low := ProverCommitRelease47.subQ _ _ _ hlo
  have high := ProverCommitRelease47.subQ _ _ _ hhi
  refine ⟨(lo,hi),?_,⟨hclo,hchi⟩,?_⟩
  · unfold field.wide_exact.WideExact.sub source pack ProverCommitRelease47.convE
    rw [low,high]
    rfl
  · apply QuadraticAlgebra.ext
    · exact hdlo
    · exact hdhi


abbrev input (x : Raw) : ProverRwDictionaryTower.W :=
  ProverRwDictionaryTower.fromW (source x)

/-- The source arithmetic is installed; only the actual canonical input
invariant remains. No source success or operation/model equality is assumed. -/
theorem correct (ops : ExternalFuns) (x y : Raw) (hx : canonical x) (hy : canonical y) :
    ∃ z : Raw,
      (ProverRwDictionaryScalar.selected ops).op97 (input x) (input y) = .ok (input z) ∧
      canonical z ∧ value z = value x - value y := by
  obtain ⟨z,hz,hc,hd⟩ := source_sub x y hx hy
  refine ⟨z,?_,hc,hd⟩
  change ProverRwDictionaryTower.mapResult ProverRwDictionaryTower.fromW
    (AspisR1ProducerRelease47.field.wide_exact.WideExact.sub
      (ProverRwDictionaryTower.toW (ProverRwDictionaryTower.fromW _))
      (ProverRwDictionaryTower.toW (ProverRwDictionaryTower.fromW _))) = _
  rw [ProverRwDictionaryTower.native_w_roundtrip,ProverRwDictionaryTower.native_w_roundtrip,hz]
  rfl

#print axioms source_sub
#print axioms correct
end R1Z.ProverRwDictionaryCorrectWSub
