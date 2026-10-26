import R1Z.ProverRwFullExternalFuns
import R1Z.PDict_PathTypesSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_PathBorrow
open Aeneas Aeneas.Std Result ProverRwFull
/-- Reuse the sibling's extracted Unix byte carriers read-only. -/
@[reducible] def native (base : ExternalTypes) : ExternalTypes :=
  { base with op2 := PDict_PathTypes.std.path.Path
              op4 := PDict_PathTypes.std.path.PathBuf }
/-- Unix PathBuf deref borrows the same bytes, without allocating or normalizing. -/
def borrow (x : PDict_PathTypes.std.path.PathBuf) :
    Result PDict_PathTypes.std.path.Path :=
  .ok ⟨⟨⟨alloc.vec.Vec.deref x.inner.inner.inner⟩⟩⟩
@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) : @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  {ops with op25 := borrow}
theorem op25_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (x : PDict_PathTypes.std.path.PathBuf) :
    (selected base ops).op25 x = .ok ⟨⟨⟨alloc.vec.Vec.deref x.inner.inner.inner⟩⟩⟩ := rfl
theorem op25_bytes (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (x : PDict_PathTypes.std.path.PathBuf) :
    ∃ p, (selected base ops).op25 x = .ok p ∧
      p.inner.inner.inner = alloc.vec.Vec.deref x.inner.inner.inner := ⟨_,rfl,rfl⟩
#print axioms op25_installed
#print axioms op25_bytes
end R1Z.PV_CB_PathBorrow
