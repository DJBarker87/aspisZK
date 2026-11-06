import PCC_ReferenceLaws
set_option autoImplicit false
namespace PCC
open PCA
def Invariant (s : PCA_State) : Prop := NLF_ParentModel.Invariant s.loans
def Preserves {α : Type} (r : Reference α) : Prop :=
  ∀ s, Invariant s → Invariant (r s).state

theorem pure_preserves {α : Type} (x : α) : Preserves (Reference.pure x) :=
  fun _ h => h

theorem error_preserves {α : Type} (e : Failure) : Preserves (Reference.error (α := α) e) :=
  fun _ h => h

theorem bind_preserves {α β : Type} (r : Reference α) (f : α → Reference β)
    (hr : Preserves r) (hf : ∀ x, Preserves (f x)) :
    Preserves (Reference.bind r f) := by
  intro s h
  have hi := hr s h
  cases he : (r s).reply with
  | ok x => simpa only [Reference.bind,he] using hf x (r s).state hi
  | error e => simpa only [Reference.bind,he] using hi
  | abort e => simpa only [Reference.bind,he] using hi

#print axioms pure_preserves
#print axioms error_preserves
#print axioms bind_preserves
end PCC
