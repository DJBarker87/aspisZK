import PV_LIB_A_SourceCellFrame14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_OperandFrame14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_LIB_A_SourceCellFrame14

def Safe : Operand → Prop
  | .move p => Local p
  | _ => True

theorem operand_frame (C : Carrier OWNER Data) (limit : Nat) (s t : Store Data)
    (w : OWNER) (a : Nat) (o : Operand) (v : Data) (later : limit ≤ a)
    (safe : Safe o) (evaluated : operand C s w a o = some (v,t)) : Below limit s t := by
  cases o with
  | constant d =>
    cases h : C.constant d with
    | none => simp [operand,h] at evaluated
    | some x =>
      simp [operand,h] at evaluated
      rcases evaluated with ⟨rfl,rfl⟩
      exact refl limit s
  | copy p =>
    cases h : PV_STX2_Store.read C s w a p with
    | none => simp [operand,h] at evaluated
    | some x =>
      simp [operand,h] at evaluated
      rcases evaluated with ⟨rfl,rfl⟩
      exact refl limit s
  | move p =>
    cases hr : PV_STX2_Store.read C s w a p with
    | none => simp [operand,hr] at evaluated
    | some x =>
      cases hp : locate C s w a p with
      | none => simp [operand,hr,hp] at evaluated
      | some q =>
        cases ht : writeAddress C s q none with
        | none => simp [operand,hr,hp,ht] at evaluated
        | some u =>
          simp [operand,hr,hp,ht] at evaluated
          rcases evaluated with ⟨rfl,rfl⟩
          apply writeAddress_frame C limit s u q none _ ht
          rw [located C s w a p q safe hp]
          exact later

theorem operands_frame (C : Carrier OWNER Data) (limit : Nat) (s t : Store Data)
    (w : OWNER) (a : Nat) (os : List Operand) (vs : List Data) (later : limit ≤ a)
    (safe : ∀ o ∈ os, Safe o) (evaluated : operands C w a os s = some (vs,t)) : Below limit s t := by
  induction os generalizing s vs with
  | nil =>
    simp [operands] at evaluated
    rcases evaluated with ⟨rfl,rfl⟩
    exact refl limit s
  | cons o os ih =>
    cases first : operand C s w a o with
    | none => simp [operands,first] at evaluated
    | some pair =>
      rcases pair with ⟨x,u⟩
      cases tail : operands C w a os u with
      | none => simp [operands,first,tail] at evaluated
      | some pair =>
        rcases pair with ⟨xs,z⟩
        simp [operands,first,tail] at evaluated
        rcases evaluated with ⟨rfl,rfl⟩
        exact trans limit s u z
          (operand_frame C limit s u w a o x later (safe o (by simp)) first)
          (ih u xs (fun p hp => safe p (by simp [hp])) tail)

#print axioms Safe
#print axioms operand_frame
#print axioms operands_frame
end PV_LIB_A_OperandFrame14
