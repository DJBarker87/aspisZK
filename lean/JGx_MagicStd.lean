import JGx_RequestRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_MagicStd
open Aeneas Aeneas.Std Result

def optionEq {T : Type} (cmp : core.cmp.PartialEq T T) (left right : Option T) : Result Bool :=
  match left,right with
  | none,none=>ok true
  | some x,some y=>cmp.eq x y
  | _,_=>ok false

def install (ops : AdapterRw.Ops) : AdapterRw.Ops :=
  {ops with op2:=optionEq,op4:=fun _ input=>ok input}

theorem source (ops : AdapterRw.Ops) (payload : Array U8 316#usize) :
    JGx_MagicGate.value (install ops) (JGx_RequestBytes.value payload)=ok false := by
  unfold JGx_MagicGate.value
  rw [JGx_RequestRead.source,bind_tc_ok]
  unfold AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC
  rfl
#print axioms source
end AspisR1.JGx_MagicStd
end
