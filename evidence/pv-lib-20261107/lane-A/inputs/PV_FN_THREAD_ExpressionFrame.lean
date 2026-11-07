import PV_FN_THREAD_LocalSourceFrame
set_option autoImplicit false
namespace PV_FN_THREAD_ExpressionFrame
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_LocalSourceFrame
/-- All expression constructors are covered; only moves can invalidate cells. -/
def Safe : Expr → Prop
  | .use o | .reference _ o | .rawPointer _ o | .unary _ o => SafeOperand o
  | .aggregate _ os => ∀ o ∈ os, SafeOperand o
  | .binary _ l r => SafeOperand l ∧ SafeOperand r
  | .nullary _ => True

theorem operands_frame {W : Type} (B : Carrier W Data) (s : Store Data) (w : W)
    (a : Nat) (os : List Operand) (vs : List Data) (t : Store Data) (p : Address)
    (outside : p.activation ≠ a) (safe : ∀ o ∈ os, SafeOperand o)
    (evaluated : operands B w a os s = some (vs,t)) : CellFrame s t p := by
  induction os generalizing s vs with
  | nil =>
    simp only [operands,Option.some.injEq,Prod.mk.injEq] at evaluated
    rcases evaluated with ⟨rfl,rfl⟩
    exact ⟨rfl,rfl⟩
  | cons o os ih =>
    cases first : operand B s w a o with
    | none => simp [operands,first] at evaluated
    | some pair =>
      rcases pair with ⟨v,u⟩
      cases tail : operands B w a os u with
      | none => simp [operands,first,tail] at evaluated
      | some pair =>
        rcases pair with ⟨ws,z⟩
        simp [operands,first,tail] at evaluated
        rcases evaluated with ⟨rfl,rfl⟩
        have head := operand_frame B s w a o v u p outside (safe o (by simp)) first
        have rest := ih u ws (by intro x hx; exact safe x (by simp [hx])) tail
        exact ⟨rest.1.trans head.1,rest.2.trans head.2⟩

theorem expression_frame {W : Type} (B : Carrier W Data) (s : Store Data) (w : W)
    (a : Nat) (e : Expr) (v : Data) (t : Store Data) (p : Address)
    (outside : p.activation ≠ a) (safe : Safe e)
    (evaluated : evaluate B s w a e = some (v,t)) : CellFrame s t p := by
  cases e with
  | use o => exact operand_frame B s w a o v t p outside safe evaluated
  | reference q o =>
    exact PV_FN_THREAD_LocalSourceFrame.expression_frame B s w a (.reference q o) v t p outside safe evaluated
  | rawPointer q o =>
    exact PV_FN_THREAD_LocalSourceFrame.expression_frame B s w a (.rawPointer q o) v t p outside safe evaluated
  | nullary op =>
    cases value : B.nullary w op <;> simp_all [evaluate,CellFrame]
  | unary op o =>
    cases arg : operand B s w a o with
    | none => simp [evaluate,arg] at evaluated
    | some pair =>
      rcases pair with ⟨x,u⟩
      cases value : B.unary op x <;> simp_all [evaluate]
      exact operand_frame B s w a o x t p outside safe arg
  | aggregate tag os =>
    cases args : operands B w a os s with
    | none => simp [evaluate,args] at evaluated
    | some pair =>
      rcases pair with ⟨xs,u⟩
      cases value : B.aggregate tag xs <;> simp_all [evaluate]
      exact operands_frame B s w a os xs t p outside safe args
  | binary op l r =>
    cases left : operand B s w a l with
    | none => simp [evaluate,left] at evaluated
    | some pair =>
      rcases pair with ⟨lv,u⟩
      cases right : operand B u w a r with
      | none => simp [evaluate,left,right] at evaluated
      | some pair =>
        rcases pair with ⟨rv,z⟩
        cases value : B.binary op lv rv <;> simp_all [evaluate]
        have first := operand_frame B s w a l lv u p outside safe.1 left
        have second := operand_frame B u w a r rv t p outside safe.2 right
        exact ⟨second.1.trans first.1,second.2.trans first.2⟩

/-- Local binding of any safe expression frames all foreign cells and the
activation counter, independently of the operand values and carrier results. -/
theorem bind_frame {W : Type} (B : Carrier W Data) (s : Store Data) (w : W)
    (a n : Nat) (e : Expr) (t : Store Data) (p : Address)
    (outside : p.activation ≠ a) (safe : Safe e)
    (bound : PV_STX2_Store.bind B s w a (.local n) e = some t) : CellFrame s t p := by
  cases val : evaluate B s w a e with
  | none => simp [PV_STX2_Store.bind,val] at bound
  | some pair =>
    rcases pair with ⟨v,u⟩
    have previous := expression_frame B s w a e v u p outside safe val
    have ne : p ≠ (⟨a,n,[]⟩ : Address) := fun eq => outside (congrArg Address.activation eq)
    simp [PV_STX2_Store.bind,val,locate,writeAddress] at bound
    subst t
    exact ⟨(write_other _ _ _ _ ne).trans previous.1,previous.2⟩
#print axioms operands_frame
#print axioms expression_frame
#print axioms bind_frame
end PV_FN_THREAD_ExpressionFrame
