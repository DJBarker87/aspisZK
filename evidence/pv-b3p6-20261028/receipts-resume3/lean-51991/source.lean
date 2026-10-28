import PV_B3P_PrefixEmission224
import PV_B3P_HelperState224
namespace PV_B3P_PrefixAction224
open Aeneas Aeneas.Std PV_B3P_224Prefix PV_B3P_RustResult
set_option autoImplicit false
abbrev Rows := Array aspis_statement.logup.CopyLogUpRow 1024#usize
abbrev Registry := Array aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1 136#usize
abbrev E := aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1

def action (view : prefix224.View) (registry : Registry) (append_index : U64)
    (lambda : aspis_core.field.QM31) (i : Nat) (rows : Rows) : Result (core.result.Result Rows E) :=
  match registry.val[i]? with
  | none => .fail .arrayOutOfBounds
  | some link => do
    let w ← prefix224.weight link.weight append_index view.withdrawal
    bindR (prefix224.side rows view link.producer link.tag w lambda false) (fun middle =>
      prefix224.side middle view link.consumer link.tag w lambda true)

def control (i : Usize) (result : Result (core.result.Result Rows E)) :
    Result (ControlFlow (Rows × Usize) (core.result.Result Rows E)) :=
  match result with
  | .fail e => .fail e
  | .div => .div
  | .ok (.Err e) => .ok (.done (.Err e))
  | .ok (.Ok rows) => .ok (.cont (rows,Usize.wrapping_add i 1#usize))

set_option backward.isDefEq.respectTransparency false in
theorem body (view : prefix224.View) (registry : Registry) (append_index : U64)
    (lambda : aspis_core.field.QM31) (rows : Rows) (i : Usize) (hi : i.val < 136) :
    prefix224.copy_rows_loop.body view registry append_index lambda rows i =
      control i (action view registry append_index lambda i.val rows) := by
  have hb : i < 136#usize := by scalar_tac
  have hlen : i.val < registry.val.length := by have h := registry.property; scalar_tac
  obtain ⟨link,hlink,hvalue⟩ := WP.spec_imp_exists (Array.index_usize_spec registry i (by
    have h := registry.property; scalar_tac))
  have hread : prefix224.link_at registry i = .ok link := hlink
  have hget : registry.val[i.val]? = some link := by
    rw [List.getElem?_eq_getElem hlen]
    rw [hvalue]
  simp only [prefix224.copy_rows_loop.body,hb,↓reduceIte,hread,bind_tc_ok,action,hget]
  cases hw : prefix224.weight link.weight append_index view.withdrawal with
  | fail e => rfl
  | div => rfl
  | ok w =>
    simp only [bind_tc_ok]
    cases hp : prefix224.side rows view link.producer link.tag w lambda false with
    | fail e => rfl
    | div => rfl
    | ok res =>
      cases res with
      | Err e => rfl
      | Ok middle =>
        simp only [bindR,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
        cases hc : prefix224.side middle view link.consumer link.tag w lambda true with
        | fail e => rfl
        | div => rfl
        | ok res => cases res <;> rfl

#print axioms body
end PV_B3P_PrefixAction224
