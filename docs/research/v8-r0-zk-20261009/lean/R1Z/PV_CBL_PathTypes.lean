import R1Z.ProverRwFullExternalFuns
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PathTypes
open ProverRwFull
set_option autoImplicit false

/-- Unix path views and owned paths are represented by their complete byte
sequence. Invalid UTF-8 is retained. The native representation relation is
separate P6 evidence; this is not a filesystem/world interpretation. -/
@[reducible] def selectedTypes (base : ExternalTypes) : ExternalTypes :=
  { base with op2 := alloc.vec.Vec U8, op4 := alloc.vec.Vec U8 }

theorem path_carrier (base : ExternalTypes) :
    @std.path.Path (selectedTypes base) = alloc.vec.Vec U8 := rfl

theorem pathbuf_carrier (base : ExternalTypes) :
    @std.path.PathBuf (selectedTypes base) = alloc.vec.Vec U8 := rfl

#print axioms path_carrier
#print axioms pathbuf_carrier
end R1Z.PV_CBL_PathTypes
