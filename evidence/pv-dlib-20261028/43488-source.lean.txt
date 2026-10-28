import R1Z.PV_DL_EncoderNative
import R1Z.PV_DL_ArrayNative
import R1Z.PV_DL_ShaRestoration
import R1Z.PV_DL_DigestFinal
import R1Z.PV_DL_FixedFinal
import R1Z.PV_DL_UpdateSelected
import R1Z.PV_DL_DefaultNative
import R1Z.PV_DL_CtSelected
open Aeneas Aeneas.Std Result ProverRwFull
noncomputable section
namespace R1Z.PV_DL_NativeCohort
set_option autoImplicit false
abbrev Types := PV_DL_ShaSelected.Types
abbrev CoreBase := PV_CBL_ShaTypes.selectedTypes

/-- One type cohort and one callback table. Each assigned entry uses its own
proved installation; untouched entries, including the compression owner, are
inherited verbatim. No new trust parameter is introduced. -/
@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (compress : PV_DL_ShaFinal.State → List U8 → Result PV_DL_ShaFinal.State)
    (shape : PV_DL_ArrayShape.Shape) : @ExternalFuns (Types base) :=
  letI : ExternalTypes := Types base
  {ops with
    op36 := (@PV_DL_ArrayNative.selected (Types base) ops).op36
    op79 := (@PV_DL_EncoderSelected.selected (Types base) ops).op79
    op205 := (PV_DL_ShaSelected.selected base ops compress).op205
    op212 := (PV_DL_DigestFinal.selected (CoreBase base) ops).op212
    op215 := (PV_DL_FixedFinal.selected (CoreBase base) ops).op215
    op216 := (PV_DL_UpdateSelected.selected (CoreBase base) ops).op216
    op217 := (PV_DL_DefaultSelected.selected (CoreBase base) ops).op217
    op219 := (PV_DL_CtSelected.selected (CoreBase base) ops shape).op219}

theorem slots (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (compress : PV_DL_ShaFinal.State → List U8 → Result PV_DL_ShaFinal.State)
    (shape : PV_DL_ArrayShape.Shape) :
    @ExternalFuns.op36 (Types base) (selected base ops compress shape)=
      @ExternalFuns.op36 (Types base) (@PV_DL_ArrayNative.selected (Types base) ops) ∧
    @ExternalFuns.op79 (Types base) (selected base ops compress shape)=
      @ExternalFuns.op79 (Types base) (@PV_DL_EncoderSelected.selected (Types base) ops) ∧
    @ExternalFuns.op205 (Types base) (selected base ops compress shape)=
      @ExternalFuns.op205 (Types base) (PV_DL_ShaSelected.selected base ops compress) ∧
    @ExternalFuns.op212 (Types base) (selected base ops compress shape)=
      @ExternalFuns.op212 (Types base) (PV_DL_DigestFinal.selected (CoreBase base) ops) ∧
    @ExternalFuns.op215 (Types base) (selected base ops compress shape)=
      @ExternalFuns.op215 (Types base) (PV_DL_FixedFinal.selected (CoreBase base) ops) ∧
    @ExternalFuns.op216 (Types base) (selected base ops compress shape)=
      @ExternalFuns.op216 (Types base) (PV_DL_UpdateSelected.selected (CoreBase base) ops) ∧
    @ExternalFuns.op217 (Types base) (selected base ops compress shape)=
      @ExternalFuns.op217 (Types base) (PV_DL_DefaultSelected.selected (CoreBase base) ops) ∧
    @ExternalFuns.op219 (Types base) (selected base ops compress shape)=
      @ExternalFuns.op219 (Types base) (PV_DL_CtSelected.selected (CoreBase base) ops shape) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms Types
#print axioms CoreBase
#print axioms selected
#print axioms slots
end R1Z.PV_DL_NativeCohort
