import PV_B3P_SelectStep227
namespace PV_B3P_SelectLoop227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_SelectIndex227 PV_B3P_SelectStep227
set_option autoImplicit false

def plan (claims : Claims) : Nat → Nat → List aspis_core.field.QM31 → List aspis_core.field.QM31
  | 0, _, out => out
  | n+1, start, out =>
    let value := if h : start < 84 then cell claims start h else aspis_core.field.QM31.ZERO
    plan claims n (start+1) (out.set start value)

def observe (x : Result Output) : Result (List aspis_core.field.QM31) :=
  match x with | .fail e => .fail e | .div => .div | .ok out => .ok out.val

theorem complete_loop (claims : Claims) (n : Nat) (out : Output) (i : Usize)
    (hi : i.val+n = 84) :
    observe (reference_terminal.select227_loop claims out i) = .ok (plan claims n i.val out.val) := by
  induction n generalizing out i with
  | zero =>
    have hs := stopped claims out i (by omega)
    unfold reference_terminal.select227_loop
    rw [loop.eq_1]
    dsimp only
    rw [hs]
    rfl
  | succ n ih =>
    have hb : i.val < 84 := by omega
    have hn := next_value i hb
    have hs := step claims out i hb
    have ht := ih (out.set i (cell claims i.val hb)) (Usize.wrapping_add i 1#usize) (by omega)
    unfold reference_terminal.select227_loop at ht ⊢
    rw [loop.eq_1]
    dsimp only
    rw [hs]
    simp only [observe,plan,hb,↓reduceDIte]
    rw [Array.set_val_eq,hn] at ht
    exact ht

theorem complete_result (claims : Claims) :
    observe (reference_terminal.select227 claims) =
      .ok (plan claims 84 0 (List.replicate 84 aspis_core.field.QM31.ZERO)) := by
  unfold reference_terminal.select227
  have h := complete_loop claims 84 (Array.repeat 84#usize aspis_core.field.QM31.ZERO) 0#usize (by rfl)
  simpa only [Array.repeat_val,show (0#usize).val = 0 from rfl] using h

#print axioms complete_loop
#print axioms complete_result
end PV_B3P_SelectLoop227
