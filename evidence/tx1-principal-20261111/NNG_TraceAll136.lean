import NNG_SourceStep136
set_option autoImplicit false
namespace AspisR1.NNG_TraceAll136
open Aeneas Aeneas.Std Result NMT_CallTree NNG_ObservationAlgebra

def All {A : Type} (P : Event → Prop) (code : Code A) : Prop := ∀ e ∈ (run code).2,P e

theorem done {A : Type} (P : Event → Prop) (a : A) : All P (.done a) := by
  intro e member
  cases member
#print axioms done

theorem lift {A : Type} (P : Event → Prop) (r : Result A) : All P (liftM r : Code A) := by
  intro e member
  cases r <;> cases member
#print axioms lift

theorem invoke {Args A : Type} (P : Event → Prop) (site : String) (args : Args) (r : Result A)
    (checked : P (.call site args r)) : All P (NMT_CallTree.invoke site args r) := by
  intro e member
  have same : e = Event.call site args r := by
    cases r <;> simpa only [NMT_CallTree.invoke,NMT_CallTree.run,List.mem_singleton] using member
  rw [same]
  exact checked
#print axioms invoke

theorem bind {A B : Type} (P : Event → Prop) (head : Code A) (next : A → Code B)
    (valid : All P head)
    (tail : ∀ a,(run head).1=.ok a → All P (next a)) : All P (NMT_CallTree.bind head next) := by
  intro e member
  rw [run_bind] at member
  change (∀ e ∈ (run head).2,P e) at valid
  generalize h : run head = out at member valid
  rcases out with ⟨reply,log⟩
  cases reply with
  | fail err => exact valid e member
  | div => exact valid e member
  | ok a =>
    rcases List.mem_append.mp member with before | after
    · exact valid e before
    · exact tail a (congrArg Prod.fst h) e after
#print axioms bind
end AspisR1.NNG_TraceAll136
