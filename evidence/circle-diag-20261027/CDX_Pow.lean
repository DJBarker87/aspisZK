-- UNCHECKED diagnostic draft: host admission/collection failed before compilation.
-- Not an accepted theorem or axiom-audit result; see CDX_FINDING.md Q2.
import RPz7_FIo_NativeFuns

set_option autoImplicit false
noncomputable section
namespace CDX.Pow
open Aeneas Aeneas.Std Result ControlFlow FIo_Native

def word (n : U32) : aspis_core.field.QM31 := ⟨⟨n,0#u32⟩,⟨0#u32,0#u32⟩⟩

theorem step_two : aspis_core.field.QM31.pow_loop.body 2#u64 (word 2#u32)
    (word 1#u32) = .ok (.cont (1#u64,word 4#u32,word 1#u32)) := by
  simp only [aspis_core.field.P, FIo_QRaw.canonical.P]
  rfl

theorem step_one : aspis_core.field.QM31.pow_loop.body 1#u64 (word 4#u32)
    (word 1#u32) = .ok (.cont (0#u64,word 16#u32,word 4#u32)) := by
  simp only [aspis_core.field.P, FIo_QRaw.canonical.P]
  rfl

theorem step_zero : aspis_core.field.QM31.pow_loop.body 0#u64 (word 16#u32)
    (word 4#u32) = .ok (.done (word 4#u32)) := by rfl

private theorem unroll (e : U64) (b a : aspis_core.field.QM31) :
    aspis_core.field.QM31.pow_loop e b a =
      (do
        let r ← aspis_core.field.QM31.pow_loop.body e b a
        match r with
        | .done v => .ok v
        | .cont (e',b',a') => aspis_core.field.QM31.pow_loop e' b' a') := by
  rw [aspis_core.field.QM31.pow_loop, loop.eq_def]
  rfl

theorem exponent_two : aspis_core.field.QM31.pow (word 2#u32) 2#u64 =
    .ok (word 4#u32) := by
  change aspis_core.field.QM31.pow_loop 2#u64 (word 2#u32) (word 1#u32) = _
  rw [unroll,step_two]
  simp only [bind_tc_ok]
  rw [unroll,step_one]
  simp only [bind_tc_ok]
  rw [unroll,step_zero]
  rfl

#print axioms step_two
#print axioms step_one
#print axioms step_zero
#print axioms exponent_two
end CDX.Pow
