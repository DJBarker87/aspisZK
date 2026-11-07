import LIB_VArithmetic
import LIB_VMask
import ExtractedMaskQM31Mul
set_option autoImplicit false
noncomputable section
namespace LIB_FieldTransport
open Aeneas Aeneas.Std LIB_VScalarCarriers
open AspisR1
abbrev PQ := AspisR1SelectedMaskProbe.field.QM31
abbrev probe := LIB_VMask.toProbe
abbrev words := ExtractedMaskQM31Mul.wordsQM
theorem words_injective {x y : PQ} (h : words x = words y) : x=y := by
 have a := UScalar.val_eq_imp x.c0.a y.c0.a (congrArg (fun w => w.1.1) h)
 have b := UScalar.val_eq_imp x.c0.b y.c0.b (congrArg (fun w => w.1.2) h)
 have c := UScalar.val_eq_imp x.c1.a y.c1.a (congrArg (fun w => w.2.1) h)
 have d := UScalar.val_eq_imp x.c1.b y.c1.b (congrArg (fun w => w.2.2) h)
 cases x with | mk x0 x1 =>
  cases x0;cases x1
  cases y with | mk y0 y1 =>
   cases y0;cases y1
   simp_all
theorem add_probe (x y : QM31) :
 AspisR1SelectedMaskProbe.field.QM31.add (probe x) (probe y) =
 .ok (probe (LIB_VArithmetic.qadd x y)) := by
 obtain ⟨n,hn,_,vn⟩ := LPi_TowerValues.qm_add x.val y.val x.property y.property
 have same := Result.ok.inj (hn.symm.trans (LIB_VArithmetic.qadd_native x y))
 subst n
 obtain ⟨p,hp,_,vp⟩ := ExtractedMaskTowerAdd.current_qm_add_mod
  (probe x) (probe y) (LIB_VMask.probe_canonical x) (LIB_VMask.probe_canonical y)
 rw [hp]
 congr 1
 apply words_injective
 exact vp.trans vn.symm
theorem mul_probe (x y : QM31) :
 AspisR1SelectedMaskProbe.field.QM31.mul (probe x) (probe y) =
 .ok (probe (LIB_VArithmetic.qmul x y)) := by
 obtain ⟨n,hn,_,vn⟩ := LPi_TowerValues.qm_mul x.val y.val x.property y.property
 have same := Result.ok.inj (hn.symm.trans (LIB_VArithmetic.qmul_native x y))
 subst n
 obtain ⟨p,hp,_,vp⟩ := ExtractedMaskQM31Mul.current_qm_mul_words
  (probe x) (probe y) (LIB_VMask.probe_canonical x) (LIB_VMask.probe_canonical y)
 rw [hp]
 congr 1
 apply words_injective
 exact vp.trans vn.symm
#print axioms words_injective
#print axioms add_probe
#print axioms mul_probe
end LIB_FieldTransport
