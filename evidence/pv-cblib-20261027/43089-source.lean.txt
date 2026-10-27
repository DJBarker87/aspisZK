import R1Z.PV_CBL_StringViewSource
import R1Z.PV_CBL_Op35Source
import R1Z.PV_CBL_PathBorrowSource
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_CBL_CallbackBundle
open ProverRwFull
set_option autoImplicit false
variable [ExternalTypes]

/-- Stable publication dictionary. Source/P6 evidence determines row credit;
this definition by itself is not a shipped/native execution instance. -/
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  PV_CBL_Op35Source.selected (PV_CBL_Op34Source.selected ops)

theorem op34_source (ops : ExternalFuns) {T : Type} (A : Type)
    (v : alloc.vec.Vec T) :
    (selected ops).op34 A v = PV_CBL_Op34Reference.empty_reference v := rfl
theorem op35_source (ops : ExternalFuns) (T : Type) :
    (selected ops).op35 T = PV_CBL_Op35Reference.default_reference T := rfl
#print axioms op35_source
#print axioms op34_source
/-- Full publication carrier for the pure path-view refinements. -/
abbrev Types (base : ExternalTypes) := PV_CBL_PathTypes.selectedTypes base

@[reducible] def selectedAll (base : ExternalTypes)
    (ops : @ExternalFuns (Types base)) : @ExternalFuns (Types base) :=
  @selected (Types base) (PV_CBL_PathBorrowSource.selected base ops)

omit [ExternalTypes] in
theorem op25_source (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (p : @std.path.PathBuf base) :
    @ExternalFuns.op25 (Types base) (selectedAll base ops) p =
      PV_CBL_PathOwnedReference.path_owned_reference base p := rfl

omit [ExternalTypes] in
theorem op29_source (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (p : @std.path.PathBuf base) :
    @ExternalFuns.op29 (Types base) (selectedAll base ops) p =
      PV_CBL_PathOwnedReference.path_owned_reference base p := rfl

omit [ExternalTypes] in
theorem op34_source_all (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    @ExternalFuns.op34 (Types base) (selectedAll base ops) T A v =
      PV_CBL_Op34Reference.empty_reference v := rfl

omit [ExternalTypes] in
theorem op35_source_all (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (T : Type) :
    @ExternalFuns.op35 (Types base) (selectedAll base ops) T =
      PV_CBL_Op35Reference.default_reference T := rfl

#print axioms op25_source
#print axioms op29_source
#print axioms op34_source_all
#print axioms op35_source_all
/-- Additional concrete string/path carrier; original publication names persist. -/
abbrev StringTypes (base : ExternalTypes) := PV_CBL_StringViewTypes.Types base
omit [ExternalTypes] in
@[reducible] def selectedString (base : ExternalTypes)
    (ops : @ExternalFuns (StringTypes base)) : @ExternalFuns (StringTypes base) :=
  PV_CBL_StringViewSource.selected base
    (selectedAll (PV_CBL_StringViewTypes.base base) ops)
omit [ExternalTypes] in
theorem op28_source (base : ExternalTypes) (ops : @ExternalFuns (StringTypes base))
    (s : String) :
    @ExternalFuns.op28 (StringTypes base) (selectedString base ops) s =
      PV_CBL_StringOwnedReference.string_owned_reference s := rfl
#print axioms op28_source
omit [ExternalTypes] in
theorem op25_source_string (base : ExternalTypes) (ops : @ExternalFuns (StringTypes base))
    (p : String) :
    @ExternalFuns.op25 (StringTypes base) (selectedString base ops) p =
      PV_CBL_PathOwnedReference.path_owned_reference (PV_CBL_StringViewTypes.base base) p := rfl
#print axioms op25_source_string
omit [ExternalTypes] in
theorem op29_source_string (base : ExternalTypes) (ops : @ExternalFuns (StringTypes base))
    (p : String) :
    @ExternalFuns.op29 (StringTypes base) (selectedString base ops) p =
      PV_CBL_PathOwnedReference.path_owned_reference (PV_CBL_StringViewTypes.base base) p := rfl
#print axioms op29_source_string
omit [ExternalTypes] in
theorem op34_source_string (base : ExternalTypes) (ops : @ExternalFuns (StringTypes base))
    {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    @ExternalFuns.op34 (StringTypes base) (selectedString base ops) T A v =
      PV_CBL_Op34Reference.empty_reference v := rfl
omit [ExternalTypes] in
theorem op35_source_string (base : ExternalTypes) (ops : @ExternalFuns (StringTypes base))
    (T : Type) :
    @ExternalFuns.op35 (StringTypes base) (selectedString base ops) T =
      PV_CBL_Op35Reference.default_reference T := rfl
omit [ExternalTypes] in
theorem op28_source_all (base : ExternalTypes) (ops : @ExternalFuns (StringTypes base))
    (s : String) :
    @ExternalFuns.op28 (StringTypes base) (selectedString base ops) s =
      PV_CBL_StringOwnedReference.string_owned_reference s := rfl
#print axioms op34_source_string
#print axioms op35_source_string
#print axioms op28_source_all
end R1Z.PV_CBL_CallbackBundle
