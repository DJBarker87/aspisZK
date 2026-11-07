import PCA_Owner
set_option autoImplicit false
namespace PCC
open PCA
/-- Child-reference execution algebra. No Children parameter. -/
abbrev Reference (α : Type) := PCA_State → Execution α
namespace Reference
def pure {α : Type} (x : α) : Reference α := fun s => ⟨s,[],.ok x⟩
def bind {α β : Type} (p : Reference α) (f : α → Reference β) : Reference β := fun s =>
  let r := p s
  match r.reply with
  | .ok x => let q := f x r.state; ⟨q.state,r.events ++ q.events,q.reply⟩
  | .error e => ⟨r.state,r.events,.error e⟩
  | .abort e => ⟨r.state,r.events,.abort e⟩
def error {α : Type} (e : Failure) : Reference α := fun s => ⟨s,[],.error e⟩
def get : Reference PCA_State := fun s => ⟨s,[],.ok s⟩
instance : Monad Reference where
  pure := pure
  bind := bind
/-- Full equality includes ordered effects and abort state, on own arguments. -/
def RowSpec {Args Reply : Type} (domain : Args → PCA_State → Prop)
    (native : Args → Reference Reply) (reference : Args → Reference Reply) : Prop :=
  ∀ args s, domain args s → native args s = reference args s
end Reference
end PCC
