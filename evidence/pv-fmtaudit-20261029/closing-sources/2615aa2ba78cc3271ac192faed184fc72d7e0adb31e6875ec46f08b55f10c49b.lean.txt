import R1Z.PV_DL_CtCarrier
import R1Z.PV_DL_DefaultCallback
open Aeneas Aeneas.Std Result ProverRwFull
noncomputable section
namespace R1Z.PV_DL_CtSelected
open PV_CBL_LibraryShapes PV_CBL_GenericArrayPower
set_option autoImplicit false
abbrev Types := PV_CBL_LibraryShapeTypes.selectedTypes

def dispatch {T A N FullA OutN OutA : Type}
    (finish : T → Buffer A → GenericArray U8 N FullA → Result (T × Buffer A × GenericArray U8 N FullA))
    (side : Result PV_DL_CtFinal.Side) (s : PV_DL_ArrayShape.Shape)
    (fallback : CtWrapper T → Buffer A → GenericArray U8 OutN OutA →
      Result (CtWrapper T × Buffer A × GenericArray U8 OutN OutA))
    (self : CtWrapper T) (buffer : Buffer A) (out : GenericArray U8 OutN OutA) :
    Result (CtWrapper T × Buffer A × GenericArray U8 OutN OutA) := by
  classical
  by_cases hf : FullA=Storage U8 5
  · subst FullA
    by_cases ho : OutA=PV_DL_ArrayShape.Carrier U8 s
    · subst OutA;exact PV_DL_CtCarrier.callback finish side s self buffer out
    · exact fallback self buffer out
  · exact fallback self buffer out

theorem dispatch_source {T A N OutN : Type}
    (finish : T → Buffer A → PV_DL_CtCarrier.Full N → Result (T × Buffer A × PV_DL_CtCarrier.Full N))
    (side : Result PV_DL_CtFinal.Side) (s : PV_DL_ArrayShape.Shape)
    (fallback : CtWrapper T → Buffer A → PV_DL_CtCarrier.Output OutN s →
      Result (CtWrapper T × Buffer A × PV_DL_CtCarrier.Output OutN s))
    (self : CtWrapper T) (buffer : Buffer A) (out : PV_DL_CtCarrier.Output OutN s) :
    dispatch finish side s fallback self buffer out=PV_DL_CtCarrier.value finish side s self buffer := by
  classical
  simp only [dispatch]
  rw [dif_pos True.intro,dif_pos True.intro]
  exact PV_DL_CtCarrier.complete finish side s self buffer out

def finisher (base : ExternalTypes) {T N0 A0 Nout Aout K N1 A1 O0 : Type}
    (vc : @digest.core_api.VariableOutputCore (Types base) T N0 A0 Nout Aout K N1 A1 O0) :
    T → Buffer A0 → GenericArray U8 Nout Aout →
      Result (T × Buffer A0 × GenericArray U8 Nout Aout) :=
  @digest.core_api.VariableOutputCore.finalize_variable_core (Types base) T N0 A0 Nout Aout K N1 A1 O0 vc

def direction (base : ExternalTypes) {T N0 A0 Nout Aout K N1 A1 O0 : Type}
    (vc : @digest.core_api.VariableOutputCore (Types base) T N0 A0 Nout Aout K N1 A1 O0) :
    Result PV_DL_CtFinal.Side :=
  @digest.core_api.VariableOutputCore.TRUNC_SIDE (Types base) T N0 A0 Nout Aout K N1 A1 O0 vc

@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (s : PV_DL_ArrayShape.Shape) : @ExternalFuns (Types base) :=
  letI : ExternalTypes := Types base
  {ops with
    op219 := fun {T OutN O N0 A0 Nout Aout K N1 A1 O0 OutA O1 O2} vc al le nz less nz1 =>
      dispatch (finisher base vc) (direction base vc) s
        (@ExternalFuns.op219 (Types base) ops T OutN O N0 A0 Nout Aout K N1 A1 O0 OutA O1 O2
          vc al le nz less nz1)}

theorem selected_native (base : ExternalTypes) (ops : @ExternalFuns (Types base))
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
  dispatch_source (finisher base vc) (direction base vc) s
    (@ExternalFuns.op219 (Types base) ops
      T OutN O N0 A0 Nout (Storage U8 5) K N1 A1 O0 (PV_DL_ArrayShape.Carrier U8 s) O1 O2
      vc al le nz less nz1) self buffer out

#print axioms Types
#print axioms dispatch
#print axioms dispatch_source
#print axioms finisher
#print axioms direction
#print axioms selected
#print axioms selected_native
end R1Z.PV_DL_CtSelected
