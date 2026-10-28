import PV_B3P_HelperLoop224
import PV_B3P_HelperList224
namespace PV_B3P_HelperComplete224
open Aeneas Aeneas.Std PV_B3P_224 PV_B3P_RustResult PV_B3P_HelperLoop224
set_option autoImplicit false

def seed : Output := Array.repeat 1024#usize aspis_core.field.QM31.ZERO

theorem observe_root (rows : Array aspis_statement.logup.CopyLogUpRow 1024#usize)
    (chi : aspis_core.field.QM31) :
    mapR (fun out : Output => out.val) (reference224.from_rows rows chi) =
      observe (reference224.from_rows_loop rows chi seed 0#usize) := by
  unfold reference224.from_rows
  change mapR (fun out : Output => out.val) (do
    let (out,pending) ← reference224.from_rows_loop rows chi seed 0#usize
    match pending with
    | none => .ok (.Ok out)
    | some result => .ok result) = _
  generalize reference224.from_rows_loop rows chi seed 0#usize = x
  cases x with
  | fail e => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨out,pending⟩
    cases pending with
    | none => rfl
    | some result => cases result <;> rfl

theorem complete_result (rows : Array aspis_statement.logup.CopyLogUpRow 1024#usize)
    (chi : aspis_core.field.QM31) :
    mapR (fun out : Output => out.val) (reference224.from_rows rows chi) =
      PV_B3P_HelperList224.ordered (PV_B3P_HelperEval224.eval rows chi) 0 1024 := by
  rw [observe_root,complete_loop rows chi 1024 seed 0#usize (by simp)]
  simp only [show (0#usize).val = 0 from rfl]
  have hlen : seed.val.length = 1024 := seed.property
  simpa only [hlen] using (PV_B3P_HelperList224.whole (PV_B3P_HelperEval224.eval rows chi) seed.val)

theorem success_values (rows : Array aspis_statement.logup.CopyLogUpRow 1024#usize)
    (chi : aspis_core.field.QM31) (out : Output)
    (h : reference224.from_rows rows chi = .ok (.Ok out)) :
    PV_B3P_HelperList224.ordered (PV_B3P_HelperEval224.eval rows chi) 0 1024 = .ok (.Ok out.val) := by
  rw [← complete_result,h]
  rfl

#print axioms observe_root
#print axioms complete_result
#print axioms success_values
end PV_B3P_HelperComplete224
