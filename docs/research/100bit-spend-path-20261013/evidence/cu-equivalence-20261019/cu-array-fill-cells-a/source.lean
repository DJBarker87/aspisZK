import CuSavingsArrayGraphLoop
import CuSavingsArrayBuilder

/-! Connect the complete emitted-loop fill to the existing callback builder.
This equation preserves arbitrary callback failure/divergence and checked-add
failure; no decoder or callback-success premise is introduced. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsArrayFillCells
open Aeneas Aeneas.Std Result
open CuSavingsArrayGraphLoop CuSavingsArrayBuilder

def store {T : Type} (buffer : Slice (Option T)) (i : Nat) : List T → Slice (Option T)
  | [] => buffer
  | value::rest => store (buffer.setAtNat i (some value)) (i+1) rest

theorem store_length {T : Type} (buffer : Slice (Option T)) (i : Nat) (values : List T) :
    (store buffer i values).length = buffer.length := by
  induction values generalizing buffer i with
  | nil => rfl
  | cons value rest ih =>
    simp only [store,ih,Slice.setAtNat_length]

theorem fill_eq_cells {T F : Type} (inst : core.ops.function.FnMut F Usize T)
    (n : Nat) (state : F) (buffer : Slice (Option T)) (i : Usize) :
    fill inst n state buffer i = (do
      let (values,_) ← cells inst n i state
      .ok (store buffer i.val values.val)) := by
  induction n generalizing state buffer i with
  | zero => rfl
  | succ n ih =>
    simp only [fill,cells]
    cases hc : inst.call_mut state i with
    | fail e => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨value,state1⟩
      simp only [bind_tc_ok]
      change (do
        let next ← UScalar.add i 1#usize
        fill inst n state1 (buffer.set i (some value)) next) =
        (do
          let (values,_) ← (do
            let next ← UScalar.add i 1#usize
            let (rest,state2) ← cells inst n next state1
            .ok ((⟨value::rest.val,by simp only [List.length_cons,rest.property]⟩ :
              {xs : List T // xs.length = n+1}),state2))
          .ok (store buffer i.val values.val))
      cases ha : UScalar.add i 1#usize with
      | fail e => rfl
      | div => rfl
      | ok next =>
        have hv := UScalar.add_equiv i 1#usize
        change (match UScalar.add i 1#usize with
          | .ok next => _
          | .fail _ => _
          | .div => _) at hv
        rw [ha] at hv
        have hnext : next.val = i.val+1 := by
          simpa only [show (1#usize).val = 1 by scalar_tac] using hv.2.1
        simp only [bind_tc_ok]
        rw [ih]
        cases hr : cells inst n next state1 with
        | fail e => rfl
        | div => rfl
        | ok pair =>
          rcases pair with ⟨rest,state2⟩
          simp only [bind_tc_ok]
          change store (buffer.set i (some value)) next.val rest.val =
            store buffer i.val (value::rest.val)
          simp only [store,Slice.set,hnext]

#print axioms store_length
#print axioms fill_eq_cells
end AspisR1.CuSavingsArrayFillCells
