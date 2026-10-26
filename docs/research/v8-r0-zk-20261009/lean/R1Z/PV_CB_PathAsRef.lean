import R1Z.PV_CB_StringPath
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_PathAsRef
open Aeneas Aeneas.Std Result ProverRwFull
@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CB_PathBorrow.native base)) :
    @ExternalFuns (PV_CB_PathBorrow.native base) :=
  letI : ExternalTypes := PV_CB_PathBorrow.native base
  {PV_CB_StringPath.selected base ops with op29 := PV_CB_PathBorrow.borrow}
theorem op29_installed (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CB_PathBorrow.native base)) (x : PDict_PathTypes.std.path.PathBuf) :
    (selected base ops).op29 x = PV_CB_PathBorrow.borrow x := rfl
theorem op29_eq_deref (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CB_PathBorrow.native base)) (x : PDict_PathTypes.std.path.PathBuf) :
    (selected base ops).op29 x = (selected base ops).op25 x := rfl
#print axioms op29_installed
#print axioms op29_eq_deref
end R1Z.PV_CB_PathAsRef
