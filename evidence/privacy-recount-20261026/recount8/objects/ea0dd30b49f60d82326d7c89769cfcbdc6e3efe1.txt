import R1Z.PV_CBL_WrapperReference
import R1Z.PV_DL_DefaultCallback
import R1Z.PV_DL_OwnershipEffects
open Aeneas Aeneas.Std Result ProverRwFull
noncomputable section
namespace R1Z.PV_DL_FixedFinal
open PV_CBL_LibraryShapes
set_option autoImplicit false
abbrev Types := PV_CBL_LibraryShapeTypes.selectedTypes

/-- Value projection for the frozen byte/word-only core. Generic destructor
and exceptional-cleanup correspondence is OwnershipEffects.complete_result. -/
def value {T A Out : Type} (finish : T → Buffer A → Out → Result (T × Buffer A × Out))
    (self : Wrapper T A) (out : Out) : Result Out :=
  match finish self.core self.buffer out with
  | .ok (_,_,produced) => ok produced
  | .fail e => fail e
  | .div => div

theorem complete {T A Out : Type} (finish : T → Buffer A → Out → Result (T × Buffer A × Out))
    (self : Wrapper T A) (out : Out) :
    PV_CBL_WrapperReference.finalize finish self out=value finish self out := by
  unfold PV_CBL_WrapperReference.finalize value
  cases finish self.core self.buffer out with
  | ok result => rcases result with ⟨core,buffer,produced⟩;rfl
  | fail e => rfl
  | div => rfl

def dispatch {T A B Out : Type} (finish : T → Buffer A → Out → Result (T × Buffer A × Out))
    (fallback : Wrapper T B → Out → Result Out) (self : Wrapper T B) (out : Out) : Result Out := by
  classical
  by_cases h : A=B
  · subst B;exact PV_CBL_WrapperReference.finalize finish self out
  · exact fallback self out

theorem dispatch_source {T A Out : Type} (finish : T → Buffer A → Out → Result (T × Buffer A × Out))
    (fallback : Wrapper T A → Out → Result Out) (self : Wrapper T A) (out : Out) :
    dispatch finish fallback self out=value finish self out := by
  classical
  simp only [dispatch]
  rw [dif_pos True.intro]
  exact complete finish self out

def finisher (base : ExternalTypes) {T N0 A0 K N1 A1 Nout Aout O0 : Type}
    (fc : @digest.core_api.FixedOutputCore (Types base) T N0 A0 K N1 A1 Nout Aout O0) :
    T → Buffer A0 → GenericArray U8 Nout Aout →
      Result (T × Buffer A0 × GenericArray U8 Nout Aout) :=
  @digest.core_api.FixedOutputCore.finalize_fixed_core (Types base) T N0 A0 K N1 A1 Nout Aout O0 fc

@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns (Types base) :=
  letI : ExternalTypes := Types base
  {ops with op215 := fun fc less nz => dispatch (finisher base fc) (ops.op215 fc less nz)}

theorem selected_native (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    {T N0 A K N1 Nout Aout O0 O1 : Type}
    (fc : @digest.core_api.FixedOutputCore (Types base) T N0 A K N1 A Nout Aout O0)
    (less : typenum.type_operators.IsLess N0 (PV_DL_DefaultCallback.Limit base) O1)
    (nz : typenum.marker_traits.NonZero O1) (self : Wrapper T A) (out : GenericArray U8 Nout Aout) :
    @ExternalFuns.op215 (Types base) (selected base ops) T N0 A K N1 A Nout Aout O0 O1 fc less nz self out=
      value (finisher base fc) self out :=
  dispatch_source (finisher base fc)
    (@ExternalFuns.op215 (Types base) ops T N0 A K N1 A Nout Aout O0 O1 fc less nz) self out

#print axioms value
#print axioms complete
#print axioms dispatch
#print axioms dispatch_source
#print axioms finisher
#print axioms selected
#print axioms selected_native
end R1Z.PV_DL_FixedFinal
