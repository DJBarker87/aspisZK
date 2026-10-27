import KSA_SmallBytes
import FIp_DotDecode
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace KSA

def emptyBytes : Slice U8 := (Array.repeat 0#usize 0#u8).to_slice
def longBytes : Slice U8 := (Array.repeat 17#usize 0#u8).to_slice

theorem emitted_qm_short : AspisR1.FIp_DotDecode.field.QM31.from_le_bytes emptyBytes = fail .panic := by
  rfl

def kitQmHasValue (bs : Slice U8) : Result Bool := do
  let v ← aspis_core.field.QM31.from_le_bytes bs
  ok v.isSome

def emittedQmHasValue (bs : Slice U8) : Result Bool := do
  let v ← AspisR1.FIp_DotDecode.field.QM31.from_le_bytes bs
  ok v.isSome

theorem qm_short_mismatch : kitQmHasValue emptyBytes ≠ emittedQmHasValue emptyBytes := by
  unfold kitQmHasValue emittedQmHasValue
  rw [emitted_qm_short]
  change ok false ≠ fail .panic
  intro h
  cases h
#print axioms emitted_qm_short
#print axioms qm_short_mismatch
end KSA
