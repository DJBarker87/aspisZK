import Aeneas
set_option autoImplicit false
namespace AspisR1.NFI_TraceResult
open Aeneas Aeneas.Std Result

/-- Partial result with retained prefix observations. A rejected continuation
never discards observations made before its rejection. -/
structure M (Cut Value : Type) where
  result : Result Value
  cuts : List Cut

def pureM {C A : Type} (a : A) : M C A := ⟨ok a,[]⟩
def bindM {C A B : Type} (before : M C A) (next : A → M C B) : M C B :=
  match before.result with
  | ok a => let after := next a; ⟨after.result,before.cuts++after.cuts⟩
  | fail e => ⟨fail e,before.cuts⟩
  | div => ⟨div,before.cuts⟩
instance {C : Type} : Monad (M C) where
  pure := pureM
  bind := bindM

def lift {C A : Type} (r : Result A) : M C A := ⟨r,[]⟩
def mark {C : Type} (c : C) : M C Unit := ⟨ok (),[c]⟩

theorem erase_bind {C A B : Type} (before : M C A) (next : A → M C B) :
    (before >>= next).result = (do let a ← before.result; (next a).result) := by
  cases before with
  | mk result cuts => cases result <;> rfl

theorem erase_lift {C A : Type} (r : Result A) : (lift r : M C A).result=r := rfl
theorem erase_mark {C : Type} (c : C) : (mark c).result=ok () := rfl
theorem erase_pure {C A : Type} (a : A) : (pure a : M C A).result=ok a := rfl

theorem fail_prefix {C A B : Type} (before : M C A) (next : A → M C B)
    (e : Error) (failure : before.result=fail e) :
    (before >>= next).result=fail e ∧ (before >>= next).cuts=before.cuts := by
  change (bindM before next).result=fail e ∧ (bindM before next).cuts=before.cuts
  simp only [bindM,failure]; exact ⟨rfl,rfl⟩

theorem div_prefix {C A B : Type} (before : M C A) (next : A → M C B)
    (failure : before.result=div) :
    (before >>= next).result=div ∧ (before >>= next).cuts=before.cuts := by
  change (bindM before next).result=div ∧ (bindM before next).cuts=before.cuts
  simp only [bindM,failure]; exact ⟨rfl,rfl⟩

#print axioms erase_bind
#print axioms erase_lift
#print axioms erase_mark
#print axioms erase_pure
#print axioms fail_prefix
#print axioms div_prefix
end AspisR1.NFI_TraceResult
