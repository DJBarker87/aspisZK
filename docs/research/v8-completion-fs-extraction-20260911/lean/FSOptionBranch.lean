import Std
set_option autoImplicit false
namespace AspisV8Completion.FSOptionBranch

def branch {A B : Type} (value : Option A)
    (onNone : B) (onSome : (a : A) → value = some a → B) : B :=
  match (generalizing := false) h : value with
  | none => onNone
  | some b => onSome b h

/-- Eliminate a proof-carrying Option match through a variable motive. This
avoids eliminating an equality whose left side is a large computed term. -/
theorem some_branch {A B : Type} (value : Option A)
    (onNone : B) (onSome : (a : A) → value = some a → B)
    (a : A) (found : value = some a) :
    branch value onNone onSome = onSome a found := by
  unfold branch
  cases value with
  | none => contradiction
  | some b =>
    have same : b = a := Option.some.inj found
    subst a
    rfl

theorem none_branch {A B : Type} (value : Option A)
    (onNone : B) (onSome : (a : A) → value = some a → B)
    (missing : value = none) :
    branch value onNone onSome = onNone := by
  unfold branch
  cases value with
  | none => rfl
  | some a => contradiction

#print axioms some_branch
#print axioms none_branch
end AspisV8Completion.FSOptionBranch
