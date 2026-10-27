import R1Z.ProverCommitMulU48
/-! Full WideExact canonical add/mul. This extends the part-47 subfield
result to arbitrary canonical high coordinates, as used by gamma/kappa folds. -/
set_option autoImplicit false
namespace R1Z.ProverCommitWideOps48
open Aeneas Aeneas.Std Result ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitRelease47
open AspisR1.ExtractedCurrentQM31Exact (decode)
abbrev Raw := Old.Q × Old.Q
abbrev Checked := AspisR1ProducerChecked47.field.wide_exact.WideExact
abbrev Source := AspisR1ProducerRelease47.field.wide_exact.WideExact
abbrev Exact := AspisWideTower.WideExact

def canonical (x : Raw) : Prop := Canonical x.1 ∧ Canonical x.2
def pack (x : Raw) : Checked := ⟨fromQ x.1,fromQ x.2⟩
def source (x : Raw) : Source := convE (pack x)
def value (x : Raw) : Exact := ⟨decode x.1,decode x.2⟩

theorem checked_add (x y : Raw) (hx : canonical x) (hy : canonical y) :
    ∃ z : Raw, AspisR1ProducerChecked47.field.wide_exact.WideExact.add (pack x) (pack y)=ok (pack z) ∧
      canonical z ∧ value z=value x+value y := by
  obtain ⟨lo,hlo,hclo,hdlo⟩ := ProverCommitQOps48.add x.1 y.1 hx.1 hy.1
  obtain ⟨hi,hhi,hchi,hdhi⟩ := ProverCommitQOps48.add x.2 y.2 hx.2 hy.2
  refine ⟨(lo,hi),?_,⟨hclo,hchi⟩,?_⟩
  · simp only [AspisR1ProducerChecked47.field.wide_exact.WideExact.add,pack,hlo,hhi,bind_tc_ok]
  · apply QuadraticAlgebra.ext
    · exact hdlo
    · exact hdhi

theorem mul_coordinates (a b c d : AspisV8R15.ExactTowerBase.QM31Exact) :
    (⟨a*c+(b*d)*AspisWideTower.wideU,(a+b)*(c+d)-a*c-b*d⟩ : Exact)=
      (⟨a,b⟩ : Exact)*⟨c,d⟩ := by
  apply QuadraticAlgebra.ext <;> simp <;> ring

theorem checked_mul (x y : Raw) (hx : canonical x) (hy : canonical y) :
    ∃ z : Raw, AspisR1ProducerChecked47.field.wide_exact.WideExact.mul (pack x) (pack y)=ok (pack z) ∧
      canonical z ∧ value z=value x*value y := by
  obtain ⟨ac,hac,hcac,hdac⟩ := ProverCommitQOps48.mul x.1 y.1 hx.1 hy.1
  obtain ⟨bd,hbd,hcbd,hdbd⟩ := ProverCommitQOps48.mul x.2 y.2 hx.2 hy.2
  obtain ⟨ab,hab,hcab,hdab⟩ := ProverCommitQOps48.add x.1 x.2 hx.1 hx.2
  obtain ⟨cd,hcd,hccd,hdcd⟩ := ProverCommitQOps48.add y.1 y.2 hy.1 hy.2
  obtain ⟨cross,hcross,hccross,hdcross⟩ := ProverCommitQOps48.mul ab cd hcab hccd
  obtain ⟨u,hu,hcu,hdu⟩ := ProverCommitMulU48.mul_u bd hcbd
  obtain ⟨lo,hlo,hclo,hdlo⟩ := ProverCommitQOps48.add ac u hcac hcu
  obtain ⟨temp,htemp,hctemp,hdtemp⟩ := ProverCommitSubtraction47.qsub_checked cross ac hccross hcac
  obtain ⟨hi,hhi,hchi,hdhi⟩ := ProverCommitSubtraction47.qsub_checked temp bd hctemp hcbd
  refine ⟨(lo,hi),?_,⟨hclo,hchi⟩,?_⟩
  · simp only [AspisR1ProducerChecked47.field.wide_exact.WideExact.mul,pack,
      hac,hbd,hab,hcd,hcross,hu,hlo,htemp,hhi,bind_tc_ok]
  · calc
      value (lo,hi)=⟨decode x.1*decode y.1+(decode x.2*decode y.2)*AspisWideTower.wideU,
          (decode x.1+decode x.2)*(decode y.1+decode y.2)-decode x.1*decode y.1-decode x.2*decode y.2⟩ := by
        apply QuadraticAlgebra.ext
        · change decode lo=_
          rw [hdlo,hdac,hdu,hdbd]
        · change decode hi=_
          rw [hdhi,hdtemp,hdcross,hdab,hdcd,hdac,hdbd]
      _ = _ := mul_coordinates _ _ _ _

theorem add_exact (x y : Raw) (hx : canonical x) (hy : canonical y) :
    ∃ z : Raw, AspisR1ProducerRelease47.field.wide_exact.WideExact.add (source x) (source y)=ok (source z) ∧
      canonical z ∧ value z=value x+value y := by
  obtain ⟨z,hz,hc,hd⟩ := checked_add x y hx hy
  exact ⟨z,ProverCommitRelease47.addE _ _ _ hz,hc,hd⟩

theorem mul_exact (x y : Raw) (hx : canonical x) (hy : canonical y) :
    ∃ z : Raw, AspisR1ProducerRelease47.field.wide_exact.WideExact.mul (source x) (source y)=ok (source z) ∧
      canonical z ∧ value z=value x*value y := by
  obtain ⟨z,hz,hc,hd⟩ := checked_mul x y hx hy
  exact ⟨z,ProverCommitRelease47.mulE _ _ _ hz,hc,hd⟩

#print axioms checked_add
#print axioms mul_coordinates
#print axioms checked_mul
#print axioms add_exact
#print axioms mul_exact
end R1Z.ProverCommitWideOps48
