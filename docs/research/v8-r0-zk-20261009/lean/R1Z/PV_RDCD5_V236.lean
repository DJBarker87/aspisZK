import R1Z.PV_RDCD5_BufferSource
import R1Z.PV_DL_UpdateSelected
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD5_V236
open Aeneas Aeneas.Std Result ProverRwFull
open PV_CBL_LibraryShapes PV_CBL_GenericArrayPower

/-- The same typed wrapper, core callback, all dead buffer bytes, and Result
carrier as the existing V236 link. No dictionary is changed or installed. -/
def typedSource {T N : Type} (update : T → PV_DL_UpdateCarrier.Blocks N → Result T)
    (self : Wrapper T (Storage U8 6)) (input : Slice U8) :
    Result (Wrapper T (Storage U8 6)) := do
  let result ← PV_RDCD5_BufferSource.source (PV_DL_UpdateCarrier.compress update)
    self.core (flatten 6 self.buffer.buffer) self.buffer.pos.val input.val
  PV_DL_UpdateCarrier.encode result

theorem carrier_instance {T N : Type} (update : T → PV_DL_UpdateCarrier.Blocks N → Result T)
    (self : Wrapper T (Storage U8 6)) (input : Slice U8)
    (hp : self.buffer.pos.val < 64) :
    typedSource update self input = PV_DL_UpdateCarrier.value update self input := by
  unfold typedSource PV_DL_UpdateCarrier.value
  rw [PV_RDCD5_BufferSource.source_instance _ _ _ _ _
    (show (flatten 6 self.buffer.buffer).length = 64 from length 6 self.buffer.buffer) hp]

/-- Instance of the existing selected op216 link at its safe private Eager64
boundary. Source/layout/codegen qualifications remain in the binding report. -/
theorem op216_instance (base : ExternalTypes)
    (ops : @ExternalFuns (PV_DL_UpdateSelected.Types base))
    {T N1 O : Type}
    (uc : @digest.core_api.UpdateCore (PV_DL_UpdateSelected.Types base) T N1 (Storage U8 6))
    (less : typenum.type_operators.IsLess (PV_AL_SplitNativeShape.Size base 6)
      (PV_DL_DefaultCallback.Limit base) O)
    (nz : typenum.marker_traits.NonZero O)
    (self : Wrapper T (Storage U8 6)) (input : Slice U8)
    (hp : self.buffer.pos.val < 64) :
    @ExternalFuns.op216 (PV_DL_UpdateSelected.Types base)
      (PV_DL_UpdateSelected.selected base ops)
      T block_buffer.Eager (PV_AL_SplitNativeShape.Size base 6) (Storage U8 6)
      N1 (Storage U8 6) O (PV_DL_UpdateSelected.bufferKind base ops T)
      uc less nz self input =
      typedSource (PV_DL_UpdateSelected.updater base uc) self input := by
  rw [PV_DL_UpdateSelected.selected_native]
  exact (carrier_instance (PV_DL_UpdateSelected.updater base uc) self input hp).symm

#print axioms carrier_instance
#print axioms op216_instance
end R1Z.PV_RDCD5_V236
