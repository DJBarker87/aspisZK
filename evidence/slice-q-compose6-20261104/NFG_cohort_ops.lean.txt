import AspisR1SemanticCallExtraction.Funs
import ExtractedMaskQM31Exact

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
open Aeneas Aeneas.Std Result

abbrev GenC := AspisR1SemanticCallExtraction.aspis_core.field.CM31
abbrev ProbeC := AspisR1SelectedMaskProbe.field.CM31
abbrev GenQ := AspisR1SemanticCallExtraction.aspis_core.field.QM31
abbrev ProbeQ := AspisR1SelectedMaskProbe.field.QM31

def genCToProbe (x : GenC) : ProbeC := ⟨x.a, x.b⟩
def genQToProbe (x : GenQ) : ProbeQ :=
  ⟨genCToProbe x.c0, genCToProbe x.c1⟩
def probeCToGen (x : ProbeC) : GenC := ⟨x.a, x.b⟩

def resultMap {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

theorem resultMap_cm_ok (a b : Std.U32) :
    resultMap genCToProbe (Result.ok (AspisR1SemanticCallExtraction.aspis_core.field.CM31.mk a b)) =
      Result.ok (AspisR1SelectedMaskProbe.field.CM31.mk a b) := rfl

theorem resultMap_qm_ok (a b : GenC) :
    resultMap genQToProbe (Result.ok (AspisR1SemanticCallExtraction.aspis_core.field.QM31.mk a b)) =
      Result.ok (AspisR1SelectedMaskProbe.field.QM31.mk (genCToProbe a) (genCToProbe b)) := rfl

theorem resultMap_bind {A B C : Type} (f : B → C) (r : Result A)
    (k : A → Result B) :
    resultMap f (r >>= k) = r >>= (fun a => resultMap f (k a)) := by
  cases r with
  | ok a => cases k a <;> rfl
  | fail e => rfl
  | div => rfl

theorem resultMap_bind_transport {A A' B B' : Type}
    (f : A → A') (g : A' → A) (hfg : ∀ a, g (f a) = a)
    (F : B → B') (r : Result A) (k : A → Result B) :
    resultMap F (r >>= k) =
      (resultMap f r) >>= (fun a' => resultMap F (k (g a'))) := by
  cases r with
  | ok a => cases k a <;> simp [resultMap, hfg]
  | fail e => rfl
  | div => rfl

theorem probeCToGen_genCToProbe (x : GenC) :
    probeCToGen (genCToProbe x) = x := by
  cases x
  rfl

theorem resultMap_genC_bind {B B' : Type} (F : B → B')
    (r : Result GenC) (k : GenC → Result B) :
    resultMap F (r >>= k) =
      (resultMap genCToProbe r) >>= (fun y =>
        resultMap F (k (probeCToGen y))) := by
  exact resultMap_bind_transport genCToProbe probeCToGen
    probeCToGen_genCToProbe F r k

theorem generated_m31_add_eq_probe (x y : Std.U32) :
    AspisR1SemanticCallExtraction.aspis_core.field.M31.add x y =
      AspisR1SelectedMaskProbe.field.M31.add x y := by
  simp only [AspisR1SemanticCallExtraction.aspis_core.field.M31.add,
    AspisR1SelectedMaskProbe.field.M31.add,
    AspisR1SemanticCallExtraction.aspis_core.field.P,
    AspisR1SelectedMaskProbe.field.P]

theorem generated_m31_sub_eq_probe (x y : Std.U32) :
    AspisR1SemanticCallExtraction.aspis_core.field.M31.sub x y =
      AspisR1SelectedMaskProbe.field.M31.sub x y := by
  simp only [AspisR1SemanticCallExtraction.aspis_core.field.M31.sub,
    AspisR1SelectedMaskProbe.field.M31.sub,
    AspisR1SemanticCallExtraction.aspis_core.field.P,
    AspisR1SelectedMaskProbe.field.P]

theorem generated_reduce_u64_eq_probe (x : Std.U64) :
    AspisR1SemanticCallExtraction.aspis_core.field.reduce_u64 x =
      AspisR1SelectedMaskProbe.field.reduce_u64 x := by
  simp only [AspisR1SemanticCallExtraction.aspis_core.field.reduce_u64,
    AspisR1SelectedMaskProbe.field.reduce_u64,
    AspisR1SemanticCallExtraction.aspis_core.field.P,
    AspisR1SelectedMaskProbe.field.P]

theorem generated_m31_mul_eq_probe (x y : Std.U32) :
    AspisR1SemanticCallExtraction.aspis_core.field.M31.mul x y =
      AspisR1SelectedMaskProbe.field.M31.mul x y := by
  simp only [AspisR1SemanticCallExtraction.aspis_core.field.M31.mul,
    AspisR1SelectedMaskProbe.field.M31.mul,
    AspisR1SemanticCallExtraction.aspis_core.field.M31.reduce_u64,
    AspisR1SelectedMaskProbe.field.M31.reduce_u64,
    generated_reduce_u64_eq_probe]

theorem generated_m31_reduce_u64_eq_probe (x : Std.U64) :
    AspisR1SemanticCallExtraction.aspis_core.field.M31.reduce_u64 x =
      AspisR1SelectedMaskProbe.field.M31.reduce_u64 x := by
  simp only [AspisR1SemanticCallExtraction.aspis_core.field.M31.reduce_u64,
    AspisR1SelectedMaskProbe.field.M31.reduce_u64,
    generated_reduce_u64_eq_probe]

theorem generated_m31_double_eq_probe (x : Std.U32) :
    AspisR1SemanticCallExtraction.aspis_core.field.M31.double x =
      AspisR1SelectedMaskProbe.field.M31.double x := by
  simp only [AspisR1SemanticCallExtraction.aspis_core.field.M31.double,
    AspisR1SelectedMaskProbe.field.M31.double, generated_m31_add_eq_probe]

theorem generated_cm_add_eq_probe (x y : GenC) :
    resultMap genCToProbe
        (AspisR1SemanticCallExtraction.aspis_core.field.CM31.add x y) =
      AspisR1SelectedMaskProbe.field.CM31.add (genCToProbe x) (genCToProbe y) := by
  change resultMap genCToProbe
      (do
        let m ← AspisR1SemanticCallExtraction.aspis_core.field.M31.add x.a y.a
        let m1 ← AspisR1SemanticCallExtraction.aspis_core.field.M31.add x.b y.b
        ok (AspisR1SemanticCallExtraction.aspis_core.field.CM31.mk m m1)) =
    do
      let m ← AspisR1SelectedMaskProbe.field.M31.add (genCToProbe x).a (genCToProbe y).a
      let m1 ← AspisR1SelectedMaskProbe.field.M31.add (genCToProbe x).b (genCToProbe y).b
      ok (AspisR1SelectedMaskProbe.field.CM31.mk m m1)
  simp only [resultMap_bind, generated_m31_add_eq_probe, genCToProbe]
  change (do
      let m ← AspisR1SelectedMaskProbe.field.M31.add x.a y.a
      let m1 ← AspisR1SelectedMaskProbe.field.M31.add x.b y.b
      Result.ok (AspisR1SelectedMaskProbe.field.CM31.mk m m1)) =
    do
      let m ← AspisR1SelectedMaskProbe.field.M31.add x.a y.a
      let m1 ← AspisR1SelectedMaskProbe.field.M31.add x.b y.b
      Result.ok (AspisR1SelectedMaskProbe.field.CM31.mk m m1)
  rfl

theorem generated_cm_sub_eq_probe (x y : GenC) :
    resultMap genCToProbe
        (AspisR1SemanticCallExtraction.aspis_core.field.CM31.sub x y) =
      AspisR1SelectedMaskProbe.field.CM31.sub (genCToProbe x) (genCToProbe y) := by
  change resultMap genCToProbe
      (do
        let m ← AspisR1SemanticCallExtraction.aspis_core.field.M31.sub x.a y.a
        let m1 ← AspisR1SemanticCallExtraction.aspis_core.field.M31.sub x.b y.b
        ok (AspisR1SemanticCallExtraction.aspis_core.field.CM31.mk m m1)) =
    do
      let m ← AspisR1SelectedMaskProbe.field.M31.sub (genCToProbe x).a (genCToProbe y).a
      let m1 ← AspisR1SelectedMaskProbe.field.M31.sub (genCToProbe x).b (genCToProbe y).b
      ok (AspisR1SelectedMaskProbe.field.CM31.mk m m1)
  simp only [resultMap_bind, generated_m31_sub_eq_probe, genCToProbe]
  change (do
      let m ← AspisR1SelectedMaskProbe.field.M31.sub x.a y.a
      let m1 ← AspisR1SelectedMaskProbe.field.M31.sub x.b y.b
      Result.ok (AspisR1SelectedMaskProbe.field.CM31.mk m m1)) =
    do
      let m ← AspisR1SelectedMaskProbe.field.M31.sub x.a y.a
      let m1 ← AspisR1SelectedMaskProbe.field.M31.sub x.b y.b
      Result.ok (AspisR1SelectedMaskProbe.field.CM31.mk m m1)
  rfl

theorem generated_cm_mul_eq_probe (x y : GenC) :
    resultMap genCToProbe
        (AspisR1SemanticCallExtraction.aspis_core.field.CM31.mul x y) =
      AspisR1SelectedMaskProbe.field.CM31.mul (genCToProbe x) (genCToProbe y) := by
  simp only [AspisR1SemanticCallExtraction.aspis_core.field.CM31.mul,
    AspisR1SelectedMaskProbe.field.CM31.mul,
    resultMap_bind, generated_m31_mul_eq_probe,
    generated_m31_reduce_u64_eq_probe, generated_m31_sub_eq_probe,
    generated_m31_add_eq_probe, resultMap_cm_ok, genCToProbe]

theorem generated_mul_by_r_eq_probe (x : GenC) :
    resultMap genCToProbe
        (AspisR1SemanticCallExtraction.aspis_core.field.mul_by_r x) =
      AspisR1SelectedMaskProbe.field.mul_by_r (genCToProbe x) := by
  simp only [AspisR1SemanticCallExtraction.aspis_core.field.mul_by_r,
    AspisR1SelectedMaskProbe.field.mul_by_r,
    resultMap_bind, generated_m31_double_eq_probe,
    generated_m31_sub_eq_probe, generated_m31_add_eq_probe,
    resultMap_cm_ok, genCToProbe]

theorem generated_qm_add_eq_probe (x y : GenQ) :
    resultMap genQToProbe
        (AspisR1SemanticCallExtraction.aspis_core.field.QM31.add x y) =
      AspisR1SelectedMaskProbe.field.QM31.add (genQToProbe x) (genQToProbe y) := by
  simp only [AspisR1SemanticCallExtraction.aspis_core.field.QM31.add,
    AspisR1SelectedMaskProbe.field.QM31.add,
    resultMap_genC_bind, generated_cm_add_eq_probe,
    resultMap_qm_ok]
  rfl

theorem generated_qm_mul_eq_probe (x y : GenQ) :
    resultMap genQToProbe
        (AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul x y) =
      AspisR1SelectedMaskProbe.field.QM31.mul (genQToProbe x) (genQToProbe y) := by
  simp only [AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul,
    AspisR1SelectedMaskProbe.field.QM31.mul,
    resultMap_genC_bind, generated_cm_mul_eq_probe,
    generated_cm_add_eq_probe, generated_cm_sub_eq_probe,
    generated_mul_by_r_eq_probe, resultMap_qm_ok]
  rfl

end AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
