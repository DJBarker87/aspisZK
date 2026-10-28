import NCV_Carrier
set_option autoImplicit false
namespace NCV_Install
open Aeneas Aeneas.Std Result

def mapReturn {A B : Type} (f : A → B) : core.result.Result A Unit →
    core.result.Result B AdapterRw.solana_program_error.ProgramError
  | .Ok a => .Ok (f a)
  | .Err () => .Err .InvalidAccountData

def op48 (b : Slice U8) := do
  let r ← NCV_Reference.decode_master_ref b
  ok (mapReturn NCV_Carrier.master r)
def op49 (b : Slice U8) := do
  let r ← NCV_Reference.decode_checkpoint_ref b
  ok (mapReturn NCV_Carrier.checkpoint r)
def op50 (b : Slice U8) := do
  let r ← NCV_Reference.decode_lane_ref b
  ok (mapReturn NCV_Carrier.lane r)

/-- Reference-body selection only. Native P6 equality is a separate gate. -/
def install (base : AdapterRw.Ops) : AdapterRw.Ops :=
  {base with op48:=op48,op49:=op49,op50:=op50}

theorem selected (base : AdapterRw.Ops) :
    (install base).op48=op48 ∧ (install base).op49=op49 ∧ (install base).op50=op50 :=
  ⟨rfl,rfl,rfl⟩

theorem pda_unchanged (base : AdapterRw.Ops) : (install base).op38=base.op38 := rfl

theorem master_result (b : Slice U8) : op48 b =
    (match NCV_Reference.decode_master_ref b with
      | .ok r => .ok (mapReturn NCV_Carrier.master r)
      | .fail e => .fail e
      | .div => .div) := by
  unfold op48
  cases NCV_Reference.decode_master_ref b <;> rfl

theorem checkpoint_result (b : Slice U8) : op49 b =
    (match NCV_Reference.decode_checkpoint_ref b with
      | .ok r => .ok (mapReturn NCV_Carrier.checkpoint r)
      | .fail e => .fail e
      | .div => .div) := by
  unfold op49
  cases NCV_Reference.decode_checkpoint_ref b <;> rfl

theorem lane_result (b : Slice U8) : op50 b =
    (match NCV_Reference.decode_lane_ref b with
      | .ok r => .ok (mapReturn NCV_Carrier.lane r)
      | .fail e => .fail e
      | .div => .div) := by
  unfold op50
  cases NCV_Reference.decode_lane_ref b <;> rfl

#print axioms selected
#print axioms pda_unchanged
#print axioms master_result
#print axioms checkpoint_result
#print axioms lane_result
end NCV_Install
