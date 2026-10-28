import Aeneas
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_OwnershipEffects
set_option autoImplicit false

/-- The world is retained on failure, so a destructor sees mutations made by
an eventually failing borrowed callback. Divergence has no final world. -/
inductive Outcome (W A : Type) where
  | success : W → A → Outcome W A
  | failure : W → Error → Outcome W A
  | divergence : Outcome W A
abbrev Effect (W A : Type) := W → Outcome W A

def erase {W A : Type} : Outcome W A → Result A
  | .success _ a => ok a
  | .failure _ e => fail e
  | .divergence => div

def unitEffect {W : Type} : Effect W Unit := fun w => .success w ()

def sequence {W : Type} (a b : Effect W Unit) : Effect W Unit := fun w =>
  match a w with
  | .success next _ => b next
  | .failure next e => .failure next e
  | .divergence => .divergence

theorem left_identity {W : Type} (drop : Effect W Unit) : sequence unitEffect drop=drop := rfl

theorem right_identity {W : Type} (drop : Effect W Unit) : sequence drop unitEffect=drop := by
  funext w
  unfold sequence
  cases h : drop w with
  | success next value => cases value;rfl
  | failure next e => rfl
  | divergence => rfl

theorem byte_buffer_drop_order {W : Type} (drop : Effect W Unit) :
    sequence drop unitEffect=sequence unitEffect drop := by
  rw [left_identity,right_identity]

/-- Both ordinary and exceptional destructor paths retain their complete
Result behavior. The double-panic policy is the same native policy on both
sides; it is not replaced by an assumption of normal destructor return. -/
def controller {W Out : Type} (finish : Effect W Out) (drop : Effect W Unit)
    (doublePanic : W → Error → Error → Outcome W Out) : Effect W Out := fun w =>
  match finish w with
  | .success next out =>
    match drop next with
    | .success done _ => .success done out
    | .failure done e => .failure done e
    | .divergence => .divergence
  | .failure next original =>
    match drop next with
    | .success done _ => .failure done original
    | .failure done later => doublePanic done original later
    | .divergence => .divergence
  | .divergence => .divergence

def native {W Out : Type} (finish : Effect W Out) (dropCore : Effect W Unit)
    (doublePanic : W → Error → Error → Outcome W Out) : Effect W Out :=
  controller finish (sequence dropCore unitEffect) doublePanic

def reference {W Out : Type} (finish : Effect W Out) (dropCore : Effect W Unit)
    (doublePanic : W → Error → Error → Outcome W Out) : Effect W Out :=
  controller finish (sequence unitEffect dropCore) doublePanic

theorem complete {W Out : Type} (finish : Effect W Out) (dropCore : Effect W Unit)
    (doublePanic : W → Error → Error → Outcome W Out) :
    native finish dropCore doublePanic=reference finish dropCore doublePanic := by
  unfold native reference
  rw [byte_buffer_drop_order]

theorem complete_result {W Out : Type} (finish : Effect W Out) (dropCore : Effect W Unit)
    (doublePanic : W → Error → Error → Outcome W Out) (w : W) :
    erase (native finish dropCore doublePanic w)=erase (reference finish dropCore doublePanic w) := by
  rw [complete]

/-- The frozen SHA byte/word-only core has no destructor. Its Result law needs
no successful-callback premise, including when failure follows state mutation. -/
theorem no_drop {W Out : Type} (finish : Effect W Out)
    (doublePanic : W → Error → Error → Outcome W Out) (w : W) :
    erase (controller finish unitEffect doublePanic w)=erase (finish w) := by
  unfold controller
  cases h : finish w <;> rfl

#print axioms Outcome
#print axioms erase
#print axioms unitEffect
#print axioms sequence
#print axioms left_identity
#print axioms right_identity
#print axioms byte_buffer_drop_order
#print axioms controller
#print axioms native
#print axioms reference
#print axioms complete
#print axioms complete_result
#print axioms no_drop
end R1Z.PV_DL_OwnershipEffects
