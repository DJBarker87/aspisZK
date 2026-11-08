import PV_LIB_A_OperandFrame14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ExpressionFrame14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_LIB_A_SourceCellFrame14 PV_LIB_A_OperandFrame14

def Safe : Expr → Prop
  | .use o | .reference _ o | .rawPointer _ o | .unary _ o => PV_LIB_A_OperandFrame14.Safe o
  | .aggregate _ os => ∀ o ∈ os, PV_LIB_A_OperandFrame14.Safe o
  | .binary _ l r => PV_LIB_A_OperandFrame14.Safe l ∧ PV_LIB_A_OperandFrame14.Safe r
  | .nullary _ => True

theorem evaluate_frame (C : Carrier OWNER Data) (limit : Nat) (s t : Store Data)
    (w : OWNER) (a : Nat) (e : Expr) (v : Data) (later : limit ≤ a)
    (safe : Safe e) (evaluated : evaluate C s w a e = some (v,t)) : Below limit s t := by
  cases e with
  | use o => exact operand_frame C limit s t w a o v later safe evaluated
  | reference p m | rawPointer p m =>
    cases address : locate C s w a p with
    | none => simp [evaluate,address] at evaluated
    | some q =>
      cases metadataRead : operand C s w a m with
      | none => simp [evaluate,address,metadataRead] at evaluated
      | some pair =>
        rcases pair with ⟨x,u⟩
        simp [evaluate,address,metadataRead] at evaluated
        rcases evaluated with ⟨rfl,rfl⟩
        exact operand_frame C limit s u w a m x later safe metadataRead
  | aggregate kind os =>
    cases args : operands C w a os s with
    | none => simp [evaluate,args] at evaluated
    | some pair =>
      rcases pair with ⟨xs,u⟩
      cases built : C.aggregate kind xs with
      | none => simp [evaluate,args,built] at evaluated
      | some x =>
        simp [evaluate,args,built] at evaluated
        rcases evaluated with ⟨rfl,rfl⟩
        exact operands_frame C limit s u w a os xs later safe args
  | unary op o =>
    cases arg : operand C s w a o with
    | none => simp [evaluate,arg] at evaluated
    | some pair =>
      rcases pair with ⟨x,u⟩
      cases built : C.unary op x with
      | none => simp [evaluate,arg,built] at evaluated
      | some y =>
        simp [evaluate,arg,built] at evaluated
        rcases evaluated with ⟨rfl,rfl⟩
        exact operand_frame C limit s u w a o x later safe arg
  | binary op l r =>
    cases left : operand C s w a l with
    | none => simp [evaluate,left] at evaluated
    | some pair =>
      rcases pair with ⟨x,u⟩
      cases right : operand C u w a r with
      | none => simp [evaluate,left,right] at evaluated
      | some pair =>
        rcases pair with ⟨y,z⟩
        cases built : C.binary op x y with
        | none => simp [evaluate,left,right,built] at evaluated
        | some b =>
          simp [evaluate,left,right,built] at evaluated
          rcases evaluated with ⟨rfl,rfl⟩
          exact trans limit s u z (operand_frame C limit s u w a l x later safe.1 left)
            (operand_frame C limit u z w a r y later safe.2 right)
  | nullary op =>
    cases built : C.nullary w op with
    | none => simp [evaluate,built] at evaluated
    | some x =>
      simp [evaluate,built] at evaluated
      rcases evaluated with ⟨rfl,rfl⟩
      exact refl limit s

/-- Local destination and local moves frame every older SOURCE cell. References
and copies may READ older cells; no alias-success or readback premise is added. -/
theorem bind_frame (C : Carrier OWNER Data) (limit : Nat) (s t : Store Data)
    (w : OWNER) (a : Nat) (dest : PV_STX2_Syntax.Place) (e : Expr) (later : limit ≤ a)
    (own : Local dest) (safe : Safe e)
    (evaluated : PV_STX2_Store.bind C s w a dest e = some t) : Below limit s t := by
  cases result : evaluate C s w a e with
  | none => simp [PV_STX2_Store.bind,result] at evaluated
  | some pair =>
    rcases pair with ⟨x,u⟩
    cases address : locate C u w a dest with
    | none => simp [PV_STX2_Store.bind,result,address] at evaluated
    | some q =>
      have write : writeAddress C u q (some x) = some t := by
        simpa [PV_STX2_Store.bind,result,address] using evaluated
      exact trans limit s u t (evaluate_frame C limit s u w a e x later safe result)
        (writeAddress_frame C limit u t q (some x)
          (by rw [located C u w a dest q own address]; exact later) write)

#print axioms Safe
#print axioms evaluate_frame
#print axioms bind_frame
end PV_LIB_A_ExpressionFrame14
