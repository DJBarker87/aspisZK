import PV_B3P_MaskCorrection14227
namespace PV_B3P_Correct14227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding10227 PV_B3P_Binding11227 PV_B3P_Success227 Result ControlFlow
set_option autoImplicit false

def clear_mask14 (mask : Nat) : Nat := mask &&& (mask-1)
def clear_times14 : Nat → Nat → Nat
  | 0,mask => mask
  | n+1,mask => clear_times14 n (clear_mask14 mask)

def mask_while_body14 (values : Array aspis_core.field.QM31 16#usize)
    (state : Nat × aspis_core.field.QM31) :
    Result (ControlFlow (Nat × aspis_core.field.QM31) aspis_core.field.QM31) :=
  if state.1 = 0 then .ok (.done state.2)
  else do
    let next ← mask_step10 values state.2 (PV_B3P_Mask227.trailing 16 state.1)
    .ok (.cont (clear_mask14 state.1,next))

def mask_while14 (values : Array aspis_core.field.QM31 16#usize) (mask : Nat)
    (sum : aspis_core.field.QM31) : Result aspis_core.field.QM31 :=
  loop (mask_while_body14 values) (mask,sum)

/-- No fuel is introduced into source execution: n is proof-only evidence that
clearing successive low set bits reaches zero. Every complete Result is kept. -/
theorem mask_while_walk14 (values : Array aspis_core.field.QM31 16#usize)
    (n mask : Nat) (sum : aspis_core.field.QM31) (terminates : clear_times14 n mask = 0) :
    mask_while14 values mask sum =
      PV_B3P_Mask227.foldResult (mask_step10 values) (PV_B3P_Mask227.walk n mask) sum := by
  unfold mask_while14
  induction n generalizing mask sum with
  | zero =>
    have zero : mask = 0 := terminates
    subst mask
    rw [loop.eq_1]
    rfl
  | succ n ih =>
    by_cases zero : mask = 0
    · subst mask
      rw [loop.eq_1]
      rfl
    · rw [loop.eq_1]
      simp only [mask_while_body14,zero,if_false,PV_B3P_Mask227.walk,PV_B3P_Mask227.foldResult]
      cases h : mask_step10 values sum (PV_B3P_Mask227.trailing 16 mask) with
      | fail e => rfl
      | div => rfl
      | ok next =>
        simp only [bind_tc_ok]
        exact ih (clear_mask14 mask) next terminates

theorem complement_off_on_domain14 (mask : U16) (allowed : MaskAllowed mask) :
    PV_B3P_Mask227.popcount mask.val ≤ 8 := by
  rcases allowed with h|h|h|h|h|h|h
  · subst mask; exact PV_B3P_Mask227.complement_off_1749
  · subst mask; exact PV_B3P_Mask227.complement_off_2048
  · subst mask; exact PV_B3P_Mask227.complement_off_2049
  · subst mask; exact PV_B3P_Mask227.complement_off_4097
  · subst mask; exact PV_B3P_Mask227.complement_off_6144
  · subst mask; exact PV_B3P_Mask227.complement_off_6145
  · subst mask; exact PV_B3P_Mask227.complement_off_26214
#print axioms mask_while_walk14
#print axioms complement_off_on_domain14
end PV_B3P_Correct14227
