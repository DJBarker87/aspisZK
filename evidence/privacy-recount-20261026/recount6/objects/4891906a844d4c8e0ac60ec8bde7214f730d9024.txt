import R1Z.ProverRwDictionaryBaseField
import AspisR1ProducerRelease47.Funs

/-! Structural ABI maps to the retained extracted field bodies. Every result
constructor, including machine failure and divergence, is preserved. Native
feature/representation/effect association remains a separate obligation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryTower
open Aeneas Aeneas.Std Result ProverRwFull
abbrev C := aspis_core.field.CM31
abbrev Q := aspis_core.field.QM31
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev NC := AspisR1ProducerRelease47.field.CM31
abbrev NQ := AspisR1ProducerRelease47.field.QM31
abbrev NW := AspisR1ProducerRelease47.field.wide_exact.WideExact

def toC (x : C) : NC := ⟨x.a,x.b⟩
def fromC (x : NC) : C := ⟨x.a,x.b⟩
def toQ (x : Q) : NQ := ⟨toC x.c0,toC x.c1⟩
def fromQ (x : NQ) : Q := ⟨fromC x.c0,fromC x.c1⟩
def toW (x : W) : NW := ⟨toQ x.c0,toQ x.c1⟩
def fromW (x : NW) : W := ⟨fromQ x.c0,fromQ x.c1⟩

theorem c_roundtrip (x : C) : fromC (toC x) = x := by cases x; rfl
theorem q_roundtrip (x : Q) : fromQ (toQ x) = x := by
  cases x with | mk a b => cases a; cases b; rfl
theorem w_roundtrip (x : W) : fromW (toW x) = x := by
  cases x with | mk a b => simp only [toW,fromW,q_roundtrip]
theorem native_c_roundtrip (x : NC) : toC (fromC x) = x := by cases x; rfl
theorem native_q_roundtrip (x : NQ) : toQ (fromQ x) = x := by
  cases x with | mk a b => cases a; cases b; rfl
theorem native_w_roundtrip (x : NW) : toW (fromW x) = x := by
  cases x with | mk a b => simp only [toW,fromW,native_q_roundtrip]

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

theorem mapResult_bind {A B : Type} (f : A → B) (r : Result A) :
    mapResult f r = (do let x ← r; .ok (f x)) := by cases r <;> rfl

def qAdd (a b : Q) : Result Q := mapResult fromQ
  (AspisR1ProducerRelease47.field.QM31.add (toQ a) (toQ b))
def qSub (a b : Q) : Result Q := mapResult fromQ
  (AspisR1ProducerRelease47.field.QM31.sub (toQ a) (toQ b))
def qMul (a b : Q) : Result Q := mapResult fromQ
  (AspisR1ProducerRelease47.field.QM31.mul (toQ a) (toQ b))
def wEmbed (a : Q) : Result W := mapResult fromW
  (AspisR1ProducerRelease47.field.wide_exact.WideExact.from_qm31 (toQ a))
def wAdd (a b : W) : Result W := mapResult fromW
  (AspisR1ProducerRelease47.field.wide_exact.WideExact.add (toW a) (toW b))
def wMul (a b : W) : Result W := mapResult fromW
  (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul (toW a) (toW b))

variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  ProverRwDictionaryBaseField.selected {ops with
    op64 := .ok (fromQ AspisR1ProducerRelease47.field.QM31.ZERO)
    op67 := qAdd, op68 := qSub, op69 := qMul
    op45 := wEmbed, op46 := wAdd, op47 := wMul}

theorem zero_installed (ops : ExternalFuns) : (selected ops).op64 =
    .ok (fromQ AspisR1ProducerRelease47.field.QM31.ZERO) := rfl

theorem q_add_installed (ops : ExternalFuns) (a b : Q) : (selected ops).op67 a b =
    mapResult fromQ (AspisR1ProducerRelease47.field.QM31.add (toQ a) (toQ b)) := rfl
theorem q_sub_installed (ops : ExternalFuns) (a b : Q) : (selected ops).op68 a b =
    mapResult fromQ (AspisR1ProducerRelease47.field.QM31.sub (toQ a) (toQ b)) := rfl
theorem q_mul_installed (ops : ExternalFuns) (a b : Q) : (selected ops).op69 a b =
    mapResult fromQ (AspisR1ProducerRelease47.field.QM31.mul (toQ a) (toQ b)) := rfl
theorem w_embed_installed (ops : ExternalFuns) (a : Q) : (selected ops).op45 a =
    mapResult fromW (AspisR1ProducerRelease47.field.wide_exact.WideExact.from_qm31 (toQ a)) := rfl
theorem w_add_installed (ops : ExternalFuns) (a b : W) : (selected ops).op46 a b =
    mapResult fromW (AspisR1ProducerRelease47.field.wide_exact.WideExact.add (toW a) (toW b)) := rfl
theorem w_mul_installed (ops : ExternalFuns) (a b : W) : (selected ops).op47 a b =
    mapResult fromW (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul (toW a) (toW b)) := rfl

#print axioms c_roundtrip
#print axioms q_roundtrip
#print axioms w_roundtrip
#print axioms native_c_roundtrip
#print axioms native_q_roundtrip
#print axioms native_w_roundtrip
#print axioms mapResult_bind
#print axioms zero_installed
#print axioms q_add_installed
#print axioms q_sub_installed
#print axioms q_mul_installed
#print axioms w_embed_installed
#print axioms w_add_installed
#print axioms w_mul_installed
end R1Z.ProverRwDictionaryTower
