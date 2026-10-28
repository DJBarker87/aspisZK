import R1Z.PV_RDB2_CBL_LibraryShapes
import R1Z.PV_RDB2_FullTypes
namespace R1Z.PV_CBL_LibraryShapeTypes
open ProverRwFull
set_option autoImplicit false

def selectedTypes (base : ExternalTypes) : ExternalTypes :=
  {base with
    op11 := PV_CBL_LibraryShapes.GenericArray
    op12 := PV_CBL_LibraryShapes.Odd
    op13 := PV_CBL_LibraryShapes.Even
    op14 := fun _ _ A _ => PV_CBL_LibraryShapes.Buffer A
    op15 := fun T _ _ A _ => PV_CBL_LibraryShapes.Wrapper T A
    op16 := fun T _ _ _ _ _ _ _ _ _ _ _ _ _ => PV_CBL_LibraryShapes.CtWrapper T}

theorem array_carrier (base : ExternalTypes) (T N A : Type) :
    @generic_array.GenericArray (selectedTypes base) T N A =
      PV_CBL_LibraryShapes.GenericArray T N A := rfl

theorem buffer_carrier (base : ExternalTypes) (N K A O : Type) :
    @block_buffer.BlockBuffer (selectedTypes base) N K A O =
      PV_CBL_LibraryShapes.Buffer A := rfl

#print axioms array_carrier
#print axioms buffer_carrier
end R1Z.PV_CBL_LibraryShapeTypes
