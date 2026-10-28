import R1Z.PV_DL_DefaultCallback
import R1Z.PV_AL_SplitNativeShape
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_DL_DefaultNative
open ProverRwFull PV_CBL_GenericArrayPower PV_CBL_LibraryShapes
open PV_DL_DefaultSelected PV_DL_DefaultCallback
set_option autoImplicit false

def bufferKind (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (T K : Type) (kind : @block_buffer.BufferKind (Types base) K) :
    @digest.core_api.BufferKindUser (Types base) T K (PV_AL_SplitNativeShape.Size base 6) (Storage U8 6) := by
  letI : ExternalTypes := Types base
  exact ⟨⟨PV_AL_SplitNativeShape.nativeTrait base ops 6⟩,kind⟩

/-- The native size constructor discharges the size guard; the core Default
operation stays a parameter with its complete Result behavior. -/
theorem native_callback (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    {T K O : Type} (dc : core.default.Default T) (kind : @block_buffer.BufferKind (Types base) K)
    (less : typenum.type_operators.IsLess (PV_AL_SplitNativeShape.Size base 6) (Limit base) O)
    (nz : typenum.marker_traits.NonZero O)
    (dn : core.default.Default (PV_AL_SplitNativeShape.Size base 6)) (dk : core.default.Default K) :
    letI : ExternalTypes := Types base
    @ExternalFuns.op217 (Types base) (PV_DL_DefaultSelected.selected base ops)
      T K (PV_AL_SplitNativeShape.Size base 6) (Storage U8 6) O dc (bufferKind base ops T K kind) less nz dn dk =
      PV_DL_DefaultBuffer.model dc.default :=
  PV_DL_DefaultCallback.callback base ops dc (bufferKind base ops T K kind)
    less nz dn dk (PV_AL_SplitNativeShape.native_size base ops)

/-- The actual generated CoreWrapper Default trait consumes the installed
operation, rather than a separate wrapper declaration. -/
theorem consumed (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    {T K O : Type} (dc : core.default.Default T) (kind : @block_buffer.BufferKind (Types base) K)
    (less : typenum.type_operators.IsLess (PV_AL_SplitNativeShape.Size base 6) (Limit base) O)
    (nz : typenum.marker_traits.NonZero O)
    (dn : core.default.Default (PV_AL_SplitNativeShape.Size base 6)) (dk : core.default.Default K) :
    letI : ExternalTypes := Types base
    (@digest.core_api.wrapper.CoreWrapper.Insts.CoreDefaultDefault (Types base)
      (PV_DL_DefaultSelected.selected base ops)
      T K (PV_AL_SplitNativeShape.Size base 6) (Storage U8 6) O dc (bufferKind base ops T K kind) less nz dn dk).default =
      PV_DL_DefaultBuffer.model dc.default :=
  native_callback base ops dc kind less nz dn dk

#print axioms bufferKind
#print axioms native_callback
#print axioms consumed
end R1Z.PV_DL_DefaultNative
