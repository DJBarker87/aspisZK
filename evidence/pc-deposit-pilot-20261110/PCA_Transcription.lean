import PCA_Owner
set_option autoImplicit false
namespace PCA
namespace Transcription
/-- Local fold rather than NHZ_DRIVER: this parent has typed SDK loans and
nonreturning abort prefixes; its result carrier differs from the TX2 driver.
This is the same source-order, SAME-prestate composition algebra. -/
def ChildPreserves (P : PCA_State → Prop) (k : Children) : Prop :=
  ∀ (α : Type) (site : Nat) (c : Call α) (s : PCA_State), P s → P (k site c s).state

def Preserves {α : Type} (P : PCA_State → Prop) (p : Plan α) : Prop :=
  ∀ (k : Children) (s : PCA_State), ChildPreserves P k → P s → P (p.run k s).state

theorem pure_preserves {α : Type} (P : PCA_State → Prop) (x : α) :
    Preserves P (Plan.pure x) := by
  intro k s _ h; exact h

theorem bind_preserves {α β : Type} (P : PCA_State → Prop) (p : Plan α) (f : α → Plan β)
    (hp : Preserves P p) (hf : ∀ x, Preserves P (f x)) :
    Preserves P (Plan.bind p f) := by
  intro k s hc hs
  have h := hp k s hc hs
  simp only [Plan.bind]
  cases hr : (p.run k s).reply with
  | ok x => exact hf x k (p.run k s).state hc h
  | error e => exact h
  | abort e => exact h

theorem call_preserves {α : Type} (P : PCA_State → Prop) (site : Nat)
    (c : Call α) (map : Failure → Failure) :
    Preserves P (Plan.call site c map) := by
  intro k s hc hs
  have h := hc α site c s hs
  simp only [Plan.call]
  cases hr : (k site c s).reply <;> exact h

theorem get_preserves (P : PCA_State → Prop) : Preserves P Plan.get := by
  intro k s _ h; exact h

theorem check_preserves (P : PCA_State → Prop) (site : Nat) (b : Bool) (e : ProgramError) :
    Preserves P (Plan.check site b e) := by
  intro k s _ h; cases b <;> exact h

theorem branch_preserves (P : PCA_State → Prop) (site : Nat) (b : Bool) :
    Preserves P (Plan.branch site b) := by
  intro k s _ h; exact h

theorem account_preserves (P : PCA_State → Prop) (site index : Nat) :
    Preserves P (Plan.account site index) := by
  intro k s _ h; exact h

#print axioms pure_preserves
#print axioms bind_preserves
#print axioms call_preserves
#print axioms get_preserves
#print axioms check_preserves
#print axioms branch_preserves
#print axioms account_preserves
end Transcription
end PCA
