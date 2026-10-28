import R1Z.PV_DL_ShaFinal
import R1Z.PV_DL_StorageBuild
import R1Z.PV_CBL_ShaTypes
import R1Z.PV_CBL_LibraryShapeTypes
import R1Z.PV_AL_SplitNativeShape
open Aeneas Aeneas.Std Result ProverRwFull
noncomputable section
namespace R1Z.PV_DL_ShaSelected
open PV_CBL_GenericArrayPower PV_CBL_LibraryShapes
set_option autoImplicit false
abbrev Types (base : ExternalTypes) :=
  PV_CBL_LibraryShapeTypes.selectedTypes (PV_CBL_ShaTypes.selectedTypes base)
abbrev Output32 (base : ExternalTypes) :=
  GenericArray U8 (PV_AL_SplitNativeShape.Size base 5) (Storage U8 5)

/-- The output's 32 bytes are all overwritten. Both changed core and changed
buffer storage are returned through the callback's actual carriers. -/
def callback (base : ExternalTypes)
    (compress : PV_DL_ShaFinal.State → List U8 → Result PV_DL_ShaFinal.State)
    (core : PV_DL_ShaFinal.Core) (buffer : Buffer (Storage U8 6)) (_ : Output32 base) :
    Result (PV_DL_ShaFinal.Core × Buffer (Storage U8 6) × Output32 base) := do
  let (core,retained,cursor,out) ← PV_DL_ShaFinal.reference compress core
    (PV_DL_StorageBuild.to64 buffer.buffer) (UScalar.cast .Usize buffer.pos)
  ok (core,⟨PV_DL_StorageBuild.build 6 (fun i => retained[i]!),0#u8,()⟩,
    ⟨PV_DL_StorageBuild.build 5 (fun i => out[i]!)⟩)

def value (base : ExternalTypes)
    (compress : PV_DL_ShaFinal.State → List U8 → Result PV_DL_ShaFinal.State)
    (core : PV_DL_ShaFinal.Core) (buffer : Buffer (Storage U8 6)) :
    Result (PV_DL_ShaFinal.Core × Buffer (Storage U8 6) × Output32 base) := do
  let (core,retained,cursor,out) ← PV_DL_ShaFinal.value compress core
    (PV_DL_StorageBuild.to64 buffer.buffer) (UScalar.cast .Usize buffer.pos)
  ok (core,⟨PV_DL_StorageBuild.build 6 (fun i => retained[i]!),0#u8,()⟩,
    ⟨PV_DL_StorageBuild.build 5 (fun i => out[i]!)⟩)

/-- Eager's native private-state invariant is pos<64. This theorem includes
all Result outcomes of an arbitrary supplied compression function. -/
theorem source_reference (base : ExternalTypes)
    (compress : PV_DL_ShaFinal.State → List U8 → Result PV_DL_ShaFinal.State)
    (core : PV_DL_ShaFinal.Core) (buffer : Buffer (Storage U8 6)) (out : Output32 base)
    (h : (UScalar.cast .Usize buffer.pos).val<64) :
    callback base compress core buffer out=value base compress core buffer := by
  unfold callback value
  rw [PV_DL_ShaFinal.source_reference compress core _ _ h]

@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (compress : PV_DL_ShaFinal.State → List U8 → Result PV_DL_ShaFinal.State) :
    @ExternalFuns (Types base) :=
  letI : ExternalTypes := Types base
  {ops with op205 := callback base compress}

theorem selected_native (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (compress : PV_DL_ShaFinal.State → List U8 → Result PV_DL_ShaFinal.State)
    (core : PV_DL_ShaFinal.Core) (buffer : Buffer (Storage U8 6)) (out : Output32 base)
    (h : (UScalar.cast .Usize buffer.pos).val<64) :
    @ExternalFuns.op205 (Types base) (selected base ops compress) core buffer out=
      value base compress core buffer := source_reference base compress core buffer out h

theorem overwrites (base : ExternalTypes)
    (compress : PV_DL_ShaFinal.State → List U8 → Result PV_DL_ShaFinal.State)
    (core : PV_DL_ShaFinal.Core) (buffer : Buffer (Storage U8 6)) (a b : Output32 base) :
    callback base compress core buffer a=callback base compress core buffer b := rfl

#print axioms Types
#print axioms Output32
#print axioms callback
#print axioms value
#print axioms source_reference
#print axioms selected
#print axioms selected_native
#print axioms overwrites
end R1Z.PV_DL_ShaSelected
