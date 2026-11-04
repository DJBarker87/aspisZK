import NFM_Control
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AspisR1.NFM_Thread
open Aeneas Aeneas.Std Result ControlFlow
abbrev Input := NFI_InnerCut.Input
abbrev Limbs := Array U64 8#usize

def window (oracle : NFF_LoggedEight.Oracle) (input : Input) (k : Fin 7)
    (limbs : Limbs) : Result Limbs := do
  let sums ← NFF_LoggedLoop.run oracle input.q input.g input.slot
    ((NFA_Iterator.cursor ⟨k.val+1,by omega⟩).val-
     (NFA_Iterator.cursor ⟨k.val,by omega⟩).val)
    {start:=NFA_Iterator.cursor ⟨k.val,by omega⟩,
     «end»:=NFA_Iterator.cursor ⟨k.val+1,by omega⟩}
    (Array.repeat 8#usize 0#u64)
  NFE_NFA_FoldEight.eight sums limbs

def thread (oracle : NFF_LoggedEight.Oracle) (input : Input) :
    List (Fin 7) → Limbs → Result Limbs
  | [],limbs => ok limbs
  | k::rest,limbs => do
    let out ← window oracle input k limbs
    thread oracle input rest out

theorem body (oracle : NFF_LoggedEight.Oracle) (input : Input) (k : Fin 7) (limbs : Limbs) :
    NFF_LoggedOuterStep.step oracle input.q input.g input.slot
      (NFA_Iterator.value ⟨k.val,by omega⟩) limbs =
    (do let out ← window oracle input k limbs
        ok (cont (NFA_Iterator.value ⟨k.val+1,by omega⟩,out))) := by
  rw [NFM_Control.body_at]
  simp only [window,bind_assoc_eq]
  rfl

theorem advance (oracle : NFF_LoggedEight.Oracle) (input : Input) (k : Fin 7)
    (fuel : Nat) (limbs : Limbs) :
    NFF_LoggedOuterLoop.run oracle input.q input.g input.slot (fuel+1)
      (NFA_Iterator.value ⟨k.val,by omega⟩) limbs =
    (do let out ← window oracle input k limbs
        NFF_LoggedOuterLoop.run oracle input.q input.g input.slot fuel
          (NFA_Iterator.value ⟨k.val+1,by omega⟩) out) := by
  rw [NFF_LoggedOuterLoop.run,body]
  cases h : window oracle input k limbs <;> rfl

theorem advance0 (oracle : NFF_LoggedEight.Oracle) (input : Input)
    (fuel : Nat) (limbs : Limbs) :
    NFF_LoggedOuterLoop.run oracle input.q input.g input.slot (fuel+1)
      (NFA_Iterator.value 0) limbs =
    (do let out ← window oracle input 0 limbs
        NFF_LoggedOuterLoop.run oracle input.q input.g input.slot fuel
          (NFA_Iterator.value 1) out) := by
  exact advance oracle input (0 : Fin 7) fuel limbs
#print axioms advance0

theorem advance1 (oracle : NFF_LoggedEight.Oracle) (input : Input)
    (fuel : Nat) (limbs : Limbs) :
    NFF_LoggedOuterLoop.run oracle input.q input.g input.slot (fuel+1)
      (NFA_Iterator.value 1) limbs =
    (do let out ← window oracle input 1 limbs
        NFF_LoggedOuterLoop.run oracle input.q input.g input.slot fuel
          (NFA_Iterator.value 2) out) := by
  exact advance oracle input (1 : Fin 7) fuel limbs
#print axioms advance1

theorem advance2 (oracle : NFF_LoggedEight.Oracle) (input : Input)
    (fuel : Nat) (limbs : Limbs) :
    NFF_LoggedOuterLoop.run oracle input.q input.g input.slot (fuel+1)
      (NFA_Iterator.value 2) limbs =
    (do let out ← window oracle input 2 limbs
        NFF_LoggedOuterLoop.run oracle input.q input.g input.slot fuel
          (NFA_Iterator.value 3) out) := by
  exact advance oracle input (2 : Fin 7) fuel limbs
#print axioms advance2

theorem advance3 (oracle : NFF_LoggedEight.Oracle) (input : Input)
    (fuel : Nat) (limbs : Limbs) :
    NFF_LoggedOuterLoop.run oracle input.q input.g input.slot (fuel+1)
      (NFA_Iterator.value 3) limbs =
    (do let out ← window oracle input 3 limbs
        NFF_LoggedOuterLoop.run oracle input.q input.g input.slot fuel
          (NFA_Iterator.value 4) out) := by
  exact advance oracle input (3 : Fin 7) fuel limbs
#print axioms advance3

theorem advance4 (oracle : NFF_LoggedEight.Oracle) (input : Input)
    (fuel : Nat) (limbs : Limbs) :
    NFF_LoggedOuterLoop.run oracle input.q input.g input.slot (fuel+1)
      (NFA_Iterator.value 4) limbs =
    (do let out ← window oracle input 4 limbs
        NFF_LoggedOuterLoop.run oracle input.q input.g input.slot fuel
          (NFA_Iterator.value 5) out) := by
  exact advance oracle input (4 : Fin 7) fuel limbs
#print axioms advance4

theorem advance5 (oracle : NFF_LoggedEight.Oracle) (input : Input)
    (fuel : Nat) (limbs : Limbs) :
    NFF_LoggedOuterLoop.run oracle input.q input.g input.slot (fuel+1)
      (NFA_Iterator.value 5) limbs =
    (do let out ← window oracle input 5 limbs
        NFF_LoggedOuterLoop.run oracle input.q input.g input.slot fuel
          (NFA_Iterator.value 6) out) := by
  exact advance oracle input (5 : Fin 7) fuel limbs
#print axioms advance5

theorem advance6 (oracle : NFF_LoggedEight.Oracle) (input : Input)
    (fuel : Nat) (limbs : Limbs) :
    NFF_LoggedOuterLoop.run oracle input.q input.g input.slot (fuel+1)
      (NFA_Iterator.value 6) limbs =
    (do let out ← window oracle input 6 limbs
        NFF_LoggedOuterLoop.run oracle input.q input.g input.slot fuel
          (NFA_Iterator.value 7) out) := by
  exact advance oracle input (6 : Fin 7) fuel limbs
#print axioms advance6

/-- Substitution threads the same mutable value from one cut into the next.
Every Result failure/divergence stops the suffix, by bind semantics. -/
theorem main (oracle : NFF_LoggedEight.Oracle) (input : Input) (limbs : Limbs) :
    thread oracle input [0,1,2,3,4,5,6] limbs =
      NFF_LoggedOuterLoop.run oracle input.q input.g input.slot 7
        (NFA_Iterator.value 0) limbs := by
  simp only [advance0,advance1,advance2,advance3,advance4,advance5,advance6,
    thread]
  rfl

#print axioms body
#print axioms advance
#print axioms main
end AspisR1.NFM_Thread
end
