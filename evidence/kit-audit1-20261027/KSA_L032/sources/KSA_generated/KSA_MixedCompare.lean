import KSA_Mixed
import FIo_NativeFuns
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace KSA

def emittedMixed : FIo_Native.aspis_core.field.QM31 :=
  ⟨⟨1#u32,0#u32⟩,⟨1#u32,0#u32⟩⟩
def emittedRaw : FIo_Native.aspis_core.field.QM31 :=
  ⟨⟨4294967295#u32,0#u32⟩,⟨4294967295#u32,0#u32⟩⟩
def emittedZero : FIo_Native.aspis_core.field.QM31 :=
  ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def emittedResult : FIo_Native.aspis_core.field.QM31 :=
  ⟨⟨3#u32,1#u32⟩,⟨2#u32,0#u32⟩⟩
theorem emitted_mixed_value :
    FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31
      ⟨emittedMixed,emittedZero⟩ emittedRaw = ok ⟨emittedResult,emittedZero⟩ := by rfl

def mixedObservation : Result U32 := do
  let w ← aspis_core.field.wide_exact.WideExact.mul_qm31
    (⟨XRn_Join_FieldExternal.oldQ mixed,XRn_Join_FieldExternal.oldQ XRn_Join_FieldExternal.qzero⟩ : XRn_Join_Wide) rawMixed
  ok w.c0.c1.a

def emittedObservation : Result U32 := do
  let w ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31
    ⟨emittedMixed,emittedZero⟩ emittedRaw
  ok w.c0.c1.a

theorem mixed_mismatch : mixedObservation ≠ emittedObservation := by
  unfold mixedObservation emittedObservation
  rw [mixed_value,emitted_mixed_value]
  decide
#print axioms emitted_mixed_value
#print axioms mixed_mismatch
end KSA
