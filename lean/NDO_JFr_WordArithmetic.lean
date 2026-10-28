import RPu_JFv_RawExtractedSemanticCallOpsV23
import ExtractedMaskQM31Mul
set_option autoImplicit false
namespace AspisR1.JFr_WordArithmetic
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
abbrev Q := AspisR1SemanticCallExtraction.aspis_core.field.QM31
abbrev Canon (x : Q) := ExtractedMaskTowerAdd.CanonicalQM (genQToProbe x)
def q (a b c d : U32) : Q := ⟨⟨a,b⟩,⟨c,d⟩⟩
def words (x : Q) : (Nat × Nat) × (Nat × Nat) := ((x.c0.a.val,x.c0.b.val),(x.c1.a.val,x.c1.b.val))
def addWords (x y : (Nat × Nat) × (Nat × Nat)) :=
  (((x.1.1+y.1.1)%2147483647,(x.1.2+y.1.2)%2147483647),
   ((x.2.1+y.2.1)%2147483647,(x.2.2+y.2.2)%2147483647))

theorem words_injective {x y : Q} (h : words x=words y) : x=y := by
  have a := UScalar.val_eq_imp x.c0.a y.c0.a (congrArg (fun w => w.1.1) h)
  have b := UScalar.val_eq_imp x.c0.b y.c0.b (congrArg (fun w => w.1.2) h)
  have c := UScalar.val_eq_imp x.c1.a y.c1.a (congrArg (fun w => w.2.1) h)
  have d := UScalar.val_eq_imp x.c1.b y.c1.b (congrArg (fun w => w.2.2) h)
  cases x with | mk x0 x1 =>
    cases x0; cases x1
    cases y with | mk y0 y1 =>
      cases y0; cases y1
      simp_all

theorem probe_words_injective {x y : AspisR1SelectedMaskProbe.field.QM31} (h : ExtractedMaskQM31Mul.wordsQM x=ExtractedMaskQM31Mul.wordsQM y) : x=y := by
  have a := UScalar.val_eq_imp x.c0.a y.c0.a (congrArg (fun w => w.1.1) h)
  have b := UScalar.val_eq_imp x.c0.b y.c0.b (congrArg (fun w => w.1.2) h)
  have c := UScalar.val_eq_imp x.c1.a y.c1.a (congrArg (fun w => w.2.1) h)
  have d := UScalar.val_eq_imp x.c1.b y.c1.b (congrArg (fun w => w.2.2) h)
  cases x with | mk x0 x1 =>
    cases x0; cases x1
    cases y with | mk y0 y1 =>
      cases y0; cases y1
      simp_all

theorem probe_injective {x y : Q} (h : genQToProbe x=genQToProbe y) : x=y := by
  apply words_injective
  exact congrArg ExtractedMaskQM31Mul.wordsQM h

theorem add (x y z : Q) (hx : Canon x) (hy : Canon y)
    (value : addWords (words x) (words y)=words z) :
    AspisR1SemanticCallExtraction.aspis_core.field.QM31.add x y=ok z := by
  obtain ⟨out,run,_,v⟩ := ExtractedMaskTowerAdd.current_qm_add_mod
    (genQToProbe x) (genQToProbe y) hx hy
  have same : out=genQToProbe z := by
    apply probe_words_injective
    exact v.trans value
  have mapped : resultMap genQToProbe (AspisR1SemanticCallExtraction.aspis_core.field.QM31.add x y)=ok (genQToProbe z) := by
    rw [generated_qm_add_eq_probe,run,same]
  obtain ⟨w,call,eq⟩ := AspisR1PublicPreparation.RawExtractedSemanticCallOpsV23.resultMap_eq_ok_inv _ _ _ mapped
  exact probe_injective eq ▸ call
#print axioms words_injective
#print axioms probe_injective

theorem mul (x y z : Q) (hx : Canon x) (hy : Canon y)
    (value : ExtractedMaskQM31Mul.qmMulWords (words x) (words y)=words z) :
    AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul x y=ok z := by
  obtain ⟨out,run,_,v⟩ := ExtractedMaskQM31Mul.current_qm_mul_words
    (genQToProbe x) (genQToProbe y) hx hy
  have same : out=genQToProbe z := probe_words_injective (v.trans value)
  have mapped : resultMap genQToProbe (AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul x y)=ok (genQToProbe z) := by
    rw [generated_qm_mul_eq_probe,run,same]
  obtain ⟨w,call,eq⟩ := AspisR1PublicPreparation.RawExtractedSemanticCallOpsV23.resultMap_eq_ok_inv _ _ _ mapped
  exact probe_injective eq ▸ call
#print axioms probe_words_injective
#print axioms add
#print axioms mul
end AspisR1.JFr_WordArithmetic
