import NET_WideModel
set_option autoImplicit false
namespace NET_FieldModel
open Aeneas Aeneas.Std Result AspisR1

theorem slot_bound (i : Usize) (slot : i.val<4) : 32*i.val+32≤128 := by omega

def part (bytes : Slice U8) (i : Usize) (size : bytes.val.length=128)
 (slot : i.val<4) : Array U8 32#usize :=
 NEO_FixedWindow.window bytes (NEO_FieldView.start i).val 32#usize (by
  have h:=NEO_FieldView.addresses i (by omega)
  change (NEO_FieldView.start i).val+32≤bytes.val.length
  rw [h.1,size]
  exact slot_bound i slot)

def field (bytes : Slice U8) (i : Usize) (size : bytes.val.length=128)
 (slot : i.val<4) : Result NET_WideModel.E := do
 let decoded ← NET_WideModel.wide (part bytes i size slot).to_slice
 core.option.Option.unwrap decoded

/-- The precise current query caller, including every malformed-window panic
prefix. No successful parse/output is supplied as an input hypothesis. -/
theorem result (bytes : Slice U8) (i : Usize) (size : bytes.val.length=128)
 (slot : i.val<4) : field bytes i size slot=FIo_Native.weights.field bytes i := by
 unfold field
 rw [NET_WideModel.result]
 symm
 exact NEO_FieldView.result bytes i (by omega) (by rw [size];exact slot_bound i slot)

theorem result_state_effects {S Event : Type} (state : S)
 (bytes : Slice U8) (i : Usize) (size : bytes.val.length=128) (slot : i.val<4) :
 NEB_PureFrame.run (Event:=Event) state (field bytes i size slot)=
 NEB_PureFrame.run state (FIo_Native.weights.field bytes i) := by
 rw [result]

#print axioms slot_bound
#print axioms result
#print axioms result_state_effects
end NET_FieldModel
