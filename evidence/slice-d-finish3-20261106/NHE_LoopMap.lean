import NHE_FieldPort
set_option autoImplicit false
namespace NHE_LoopMap
open Aeneas Aeneas.Std Result ControlFlow AspisR1

def control {S T A B : Type} (stateMap : S → T) (resultMap : A → B) : ControlFlow S A → ControlFlow T B
 | .cont s => .cont (stateMap s)
 | .done a => .done (resultMap a)

theorem finite {S T A B : Type} (left : S → Result (ControlFlow S A))
 (right : T → Result (ControlFlow T B)) (sm : S → T) (rm : A → B) (rank : S → Nat)
 (step : ∀ s,FIo_FieldBridge.map (control sm rm) (left s)=right (sm s))
 (decreases : ∀ s n,left s=ok (.cont n) → rank n<rank s) (s : S) :
 FIo_FieldBridge.map rm (loop left s)=loop right (sm s) := by
 have go : ∀ k s,rank s=k → FIo_FieldBridge.map rm (loop left s)=loop right (sm s) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
   intro s hs
   rw [loop.eq_def,loop.eq_def,←step s]
   cases hl : left s with
   | fail e => rfl
   | div => rfl
   | ok cf =>
    cases cf with
    | done a => rfl
    | cont n =>
     have less : rank n<k := by rw [←hs];exact decreases s n hl
     exact ih (rank n) less n rfl
 exact go (rank s) s rfl

#print axioms finite
end NHE_LoopMap
