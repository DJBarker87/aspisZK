import NEG_DotDomain
set_option autoImplicit false
namespace NEV_DotSchedule
/-- Mathematical schedule only. No theorem below claims the Rust standard
library's private StepBy representation is already bridged. -/
def start (batch : Nat) := 4*batch
def stop (batch : Nat) := min (start batch+4) 26

theorem block (batch : Nat) (active : batch<7) :
    start batch<stop batch ∧ stop batch≤26 ∧ stop batch-start batch≤4 := by
  simp only [stop,start]
  omega

theorem reached (batch term : Nat) (active : batch<7)
    (lower : start batch≤term) (upper : term<stop batch) :
    term<26 ∧ term-start batch<4 := by
  simp only [stop,start] at *
  omega

theorem unique_block (term : Nat) (inside : term<26) :
    term/4<7 ∧ start (term/4)≤term ∧ term<stop (term/4) := by
  simp only [stop,start]
  omega

theorem remaining (batch : Nat) (bounded : batch≤7) :
    (26-start batch+3)/4=7-batch := by unfold start;omega

theorem adjacent (batch : Nat) (active : batch<6) : stop batch=start (batch+1) := by
  simp only [stop,start]
  omega
/-- These are the reviewed specialization's NATURAL equations, still subject
 to the OPEN native/model state association and missing matched control. -/
def counts (batch : Nat) : Nat×Nat := (start batch,7-batch)
def advance (state : Nat×Nat) : Option (Nat×(Nat×Nat)) :=
 if state.2>0 then some (state.1,(state.1+4,state.2-1)) else none

theorem advance_mathematics (batch : Nat) (active : batch<7) :
    advance (counts batch)=some (start batch,counts (batch+1)) := by
  unfold advance counts
  dsimp only
  rw [if_pos (by omega)]
  apply congrArg some
  apply Prod.ext rfl
  apply Prod.ext <;> unfold start <;> omega

theorem finished : advance (counts 7)=none := by rfl
#print axioms block
#print axioms reached
#print axioms unique_block
#print axioms remaining
#print axioms adjacent
#print axioms advance_mathematics
#print axioms finished
end NEV_DotSchedule
