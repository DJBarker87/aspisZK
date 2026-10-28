import R1Z.PV_RDB2_ResumeAudit

/-! One focused replay of the three restored row laws in the frozen owned cohort.
These are source-helper/model laws; endpoint and compiler premises are retained. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDB2_ResumeReplay
open Aeneas Aeneas.Std Result ProverRwFull

section
variable [ExternalTypes]
theorem compressor (ops : ExternalFuns) :
    PV_Op223_Applied.prover_shared.compress_tagged_tuple =
      @ProverRwP6CompressSource.compress _ (PV_RDB2_Compress.primitives ops) :=
  PV_RDB2_Compress.complete ops

theorem sum (ops : ExternalFuns) (xs : Slice aspis_core.field.QM31) :
    (PV_RDB2_SumDeployed.selected ops).op230 xs =
      ok (Option.map PV_B1_ActualCarrier230.fromQ
        (PV_B1_SumOriginal.original_row
          (PV_B1_Transport.sliceMap PV_B1_ActualCarrier230.toQ xs))) :=
  PV_RDB2_SumDeployed.installed ops xs
end

open PV_CBL_LibraryShapes PV_CBL_GenericArrayPower PV_DL_CtSelected
theorem ct_wrapper (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (s : PV_DL_ArrayShape.Shape) {T OutN O N0 A0 Nout K N1 A1 O0 O1 O2 : Type}
    (vc : @digest.core_api.VariableOutputCore (Types base) T N0 A0 Nout (Storage U8 5) K N1 A1 O0)
    (al : generic_array.ArrayLength OutN U8 (PV_DL_ArrayShape.Carrier U8 s))
    (le : typenum.type_operators.IsLessOrEqual OutN Nout O1) (nz : typenum.marker_traits.NonZero O1)
    (less : typenum.type_operators.IsLess N0 (PV_DL_DefaultCallback.Limit base) O2)
    (nz1 : typenum.marker_traits.NonZero O2)
    (self : CtWrapper T) (buffer : Buffer A0) (out : PV_DL_CtCarrier.Output OutN s) :
    @ExternalFuns.op219 (Types base) (selected base ops s)
      T OutN O N0 A0 Nout (Storage U8 5) K N1 A1 O0 (PV_DL_ArrayShape.Carrier U8 s) O1 O2
      vc al le nz less nz1 self buffer out=
      PV_DL_CtCarrier.value (finisher base vc) (direction base vc) s self buffer :=
  PV_DL_CtSelected.selected_native base ops s vc al le nz less nz1 self buffer out

#print axioms compressor
#print axioms sum
#print axioms ct_wrapper
end R1Z.PV_RDB2_ResumeReplay
