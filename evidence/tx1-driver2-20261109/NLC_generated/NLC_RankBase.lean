import NLC_FrameAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Source order, with nested callback markers excluded from normal dispatch. -/
def rank : Event → Nat
 | .rounds => 0
 | .mark2 => 1
 | .claims => 2
 | .original => 3
 | .terminal => 4
 | .mapPublic => 5
 | .mark3 => 6
 | .lowArray => 7
 | .highArray => 8
 | .blind => 9
 | .alpha => 10
 | .mask => 11
 | .record25a => 12
 | .decode25 => 13
 | .multiply => 14
 | .addMask => 15
 | .extra28 => 16
 | .addExtra => 17
 | .terminalGuard => 18
 | .mark4 => 19
 | .stateBefore => 20
 | .record25b => 21
 | .circle0 => 22
 | .record26a => 23
 | .decode26 => 24
 | .record26b => 25
 | .circle1 => 26
 | .mark5 => 27
 | .circleGuard => 28
 | .payload2 => 29
 | .rootCopy => 30
 | .verified => 31
 | .lowIndex => 32
 | .highIndex => 33

def RankPost {H : Type} (s : State H) : Post H → Prop
 | .inl _ => True
 | .inr after => rank after.next = rank s.next + 1

theorem rank_put {H : Type} (s : State H) (e : Event) (l : Locals H)
 (order : rank e = rank s.next + 1) : RankPost s (.inr (put s e l)) := order

theorem rank_next {H : Type} (s : State H) (e : Event)
 (order : rank e = rank s.next + 1) : RankPost s (.inr (setNext s e)) := order

theorem rank_returned {A H : Type} (s : State H) (e : Event)
 (r : core.result.Result A r1_wire.Error) (store : A → Locals H)
 (order : rank e = rank s.next + 1) : RankPost s (returned s e r store) := by
 cases r with
 | Ok a => exact order
 | Err e => trivial

theorem rank_bound (e : Event) : rank e < 34 := by cases e <;> decide
#print axioms rank_put
#print axioms rank_next
#print axioms rank_returned
#print axioms rank_bound
end AspisR1.NLC_Finish
end
