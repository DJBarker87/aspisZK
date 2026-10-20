import CurrentWideField
import FoldInversesExplicitOps
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
abbrev FoldE := AspisR1FoldInverses.aspis_core.field.WideExact
abbrev FoldCM := AspisR1FoldInverses.aspis_core.field.CM31
abbrev FoldQM := AspisR1FoldInverses.aspis_core.field.QM31

def ofFoldCM (x : FoldCM) : field.CM31 := ⟨x.a,x.b⟩
def ofFoldQM (x : FoldQM) : field.QM31 := ⟨ofFoldCM x.c0,ofFoldCM x.c1⟩
def ofFoldE (x : FoldE) : E := ⟨ofFoldQM x.c0,ofFoldQM x.c1⟩
def toFoldCM (x : field.CM31) : FoldCM := ⟨x.a,x.b⟩
def toFoldQM (x : field.QM31) : FoldQM := ⟨toFoldCM x.c0,toFoldCM x.c1⟩
def toFoldE (x : E) : FoldE := ⟨toFoldQM x.c0,toFoldQM x.c1⟩

theorem to_of_fold (x : FoldE) : toFoldE (ofFoldE x)=x := rfl
theorem of_to_fold (x : E) : ofFoldE (toFoldE x)=x := rfl

def runBinary (f : E → E → Result E) (x y : FoldE) : Result FoldE := do
  let z ← f (ofFoldE x) (ofFoldE y)
  ok (toFoldE z)
def runScale (x : FoldE) (s : U32) : Result FoldE := do
  let z ← field.wide_exact.WideExact.mul_m31 (ofFoldE x) s
  ok (toFoldE z)
def currentFoldOps : AspisR1FoldInverses.FoldOps where
  add := runBinary field.wide_exact.WideExact.add
  sub := runBinary field.wide_exact.WideExact.sub
  mul := runBinary field.wide_exact.WideExact.mul
  scale := runScale
  baseMul := field.M31.mul

def CanonicalFold (x : FoldE) : Prop := CanonicalWide (ofFoldE x)
def decodeFold (x : FoldE) : AspisWideTower.WideExact := decodeWide (ofFoldE x)

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem runBinary_success (f : E → E → Result E) (x y z : FoldE)
    (h : runBinary f x y = .ok z) :
    ∃ out, f (ofFoldE x) (ofFoldE y) = .ok out ∧ ofFoldE z=out := by
  unfold runBinary at h
  rcases bind_ok_inv h with ⟨out,ho,h⟩
  have he : toFoldE out=z := Result.ok.inj h
  exact ⟨out,ho,by rw [←he,of_to_fold]⟩

theorem current_fold_add (x y z : FoldE) (hx : CanonicalFold x) (hy : CanonicalFold y)
    (h : currentFoldOps.add x y = .ok z) :
    CanonicalFold z ∧ decodeFold z=decodeFold x+decodeFold y := by
  obtain ⟨out,ho,hz⟩ := runBinary_success field.wide_exact.WideExact.add x y z h
  have hr := wide_add_success (ofFoldE x) (ofFoldE y) out hx hy ho
  change CanonicalWide (ofFoldE z) ∧ decodeWide (ofFoldE z)=decodeWide (ofFoldE x)+decodeWide (ofFoldE y)
  rw [hz]
  exact hr

#print axioms to_of_fold
#print axioms of_to_fold
#print axioms runBinary_success
#print axioms current_fold_add
end AspisR1CurrentWide.Proof
