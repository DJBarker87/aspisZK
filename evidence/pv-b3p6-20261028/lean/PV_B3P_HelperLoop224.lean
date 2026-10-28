import PV_B3P_HelperStep224
import PV_B3P_HelperAbort224
import PV_B3P_HelperEval224
import PV_B3P_HelperPlan224
import PV_B3P_MaskLoopBounds132
namespace PV_B3P_HelperLoop224
open Aeneas Aeneas.Std PV_B3P_224 PV_B3P_RustResult
set_option autoImplicit false

abbrev Output := Array aspis_core.field.QM31 1024#usize
abbrev Pending := Option (core.result.Result Output reference224.Error)
def observe (x : Result (Output × Pending)) : Result (core.result.Result (List aspis_core.field.QM31) reference224.Error) :=
  match x with
  | .fail e => .fail e
  | .div => .div
  | .ok (out,none) => .ok (.Ok out.val)
  | .ok (_,some (.Err e)) => .ok (.Err e)
  | .ok (_,some (.Ok out)) => .ok (.Ok out.val)

theorem complete_loop (rows : Array aspis_statement.logup.CopyLogUpRow 1024#usize)
    (chi : aspis_core.field.QM31) (n : Nat) (out : Output) (r : Usize)
    (hr : r.val+n = 1024) :
    observe (reference224.from_rows_loop rows chi out r) =
      PV_B3P_HelperPlan224.run (PV_B3P_HelperEval224.eval rows chi) r.val n out.val := by
  induction n generalizing out r with
  | zero =>
    have hs := PV_B3P_HelperStep224.stopped rows chi out r (by omega)
    unfold reference224.from_rows_loop
    rw [loop.eq_1]
    dsimp only
    rw [hs]
    rfl
  | succ n ih =>
    have hb : r.val < 1024 := by omega
    have hnext := (PV_B3P_MaskLoopBounds132.row_next r hb).1
    cases he : reference224.one_row (PV_B3P_HelperRead224.rowValue rows r hb) chi with
    | fail e =>
      have hs := PV_B3P_HelperAbort224.failure rows chi out r hb e he
      unfold reference224.from_rows_loop
      rw [loop.eq_1]
      dsimp only
      rw [hs]
      simp only [observe,PV_B3P_HelperPlan224.run,PV_B3P_HelperEval224.at_index rows chi r hb,he,bindR]
    | div =>
      have hs := PV_B3P_HelperAbort224.divergence rows chi out r hb he
      unfold reference224.from_rows_loop
      rw [loop.eq_1]
      dsimp only
      rw [hs]
      simp only [observe,PV_B3P_HelperPlan224.run,PV_B3P_HelperEval224.at_index rows chi r hb,he,bindR]
    | ok res =>
      cases res with
      | Err e =>
        have hs := PV_B3P_HelperStep224.rejection rows chi out r hb e he
        unfold reference224.from_rows_loop
        rw [loop.eq_1]
        dsimp only
        rw [hs]
        simp only [observe,PV_B3P_HelperPlan224.run,PV_B3P_HelperEval224.at_index rows chi r hb,he,bindR]
      | Ok value =>
        have hs := PV_B3P_HelperStep224.success rows chi out r hb value he
        have ht := ih (out.set r value) (Usize.wrapping_add r 1#usize) (by omega)
        unfold reference224.from_rows_loop at ht ⊢
        rw [loop.eq_1]
        dsimp only
        rw [hs]
        simp only [PV_B3P_HelperPlan224.run,PV_B3P_HelperEval224.at_index rows chi r hb,he,bindR]
        rw [Array.set_val_eq,hnext] at ht
        exact ht

#print axioms complete_loop
end PV_B3P_HelperLoop224
