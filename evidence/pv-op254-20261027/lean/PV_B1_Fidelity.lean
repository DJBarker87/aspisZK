import PV_B1_254_Funs
set_option autoImplicit false
namespace PV_B1_Fidelity
open Aeneas Aeneas.Std Result ControlFlow PV_B1_254
abbrev W := aspis_core.field.wide_exact.WideExact
-- The ignored component is the old value. The backward function is retained.
theorem restoration {N : Usize} (out : Array W N) (i : Usize) (old value : W)
    (h : Array.index_usize out i=ok old) :
    (do let (_,back) ← Array.index_mut_usize out i
        ok (back value)) = ok (Aeneas.Std.Array.set out i value) := by
  unfold Array.index_mut_usize
  rw [h]
  rfl
#print axioms restoration
-- Direct execution of the emitted body, not an independently written loop.
#eval (match powers_loop.body (N:=1#usize) aspis_core.field.wide_exact.WideExact.ZERO
    (Array.repeat 1#usize aspis_core.field.wide_exact.WideExact.ZERO)
    aspis_core.field.wide_exact.WideExact.ONE 0#usize with
  | .ok (.cont (out,_,_)) => out.val.map (fun w => w.c0.c0.a.val)
  | _ => [])
#eval (match powers_loop.body (N:=2#usize) aspis_core.field.wide_exact.WideExact.ZERO
    (Array.repeat 2#usize aspis_core.field.wide_exact.WideExact.ZERO)
    aspis_core.field.wide_exact.WideExact.ONE 0#usize with
  | .ok (.cont (out,_,_)) => out.val.map (fun w => w.c0.c0.a.val)
  | _ => [])
end PV_B1_Fidelity
