import R1Z.PV_W_ReachedEffects
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_Callbacks
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects
variable [ExternalTypes]

abbrev Hash := Slice (Slice U8) → P (Array U8 32#usize)
structure Store (T : Type) where
  reserve : T → Array U8 32#usize → Array U8 32#usize → P (Bool × T)

def sourceHash (ops : ExternalFuns) (hash : Hash) :
    Slice (Slice U8) → Aeneas.Std.Result (Array U8 32#usize) := fun a => erase ops (hash a)
def sourceStore {T : Type} (ops : ExternalFuns) (store : Store T) :
    aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T :=
  { «reserve» := fun s a b => erase ops (store.reserve s a b) }

theorem erase_hash (ops : ExternalFuns) (hash : Hash) (a : Slice (Slice U8)) :
    erase ops (hash a) = sourceHash ops hash a := rfl

theorem erase_store {T : Type} (ops : ExternalFuns) (store : Store T)
    (s : T) (a b : Array U8 32#usize) :
    erase ops (store.reserve s a b) = (sourceStore ops store).«reserve» s a b := rfl

theorem erase_ite {A : Type} (ops : ExternalFuns) (p : Prop) [Decidable p]
    (yes no : P A) : erase ops (if p then yes else no) =
      if p then erase ops yes else erase ops no := by
  by_cases h : p <;> simp only [h,↓reduceIte]

theorem erase_if_congr {A : Type} (ops : ExternalFuns) (p : Prop) [Decidable p]
    (yes no : P A) (left right : Aeneas.Std.Result A)
    (hy : erase ops yes = left) (hn : erase ops no = right) :
    erase ops (if p then yes else no) = if p then left else right := by
  rw [erase_ite,hy,hn]

#print axioms erase_hash
#print axioms erase_store
#print axioms erase_ite
#print axioms erase_if_congr
end R1Z.PV_W_Callbacks
