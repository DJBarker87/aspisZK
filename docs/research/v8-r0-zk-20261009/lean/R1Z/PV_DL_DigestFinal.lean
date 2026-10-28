import R1Z.PV_DL_StorageBuild
import R1Z.PV_CBL_LibraryShapeTypes
import R1Z.ProverRwFullExternalFuns
open Aeneas Aeneas.Std Result ProverRwFull
noncomputable section
namespace R1Z.PV_DL_DigestFinal
open PV_CBL_GenericArrayPower PV_CBL_LibraryShapes
set_option autoImplicit false
abbrev Types := PV_CBL_LibraryShapeTypes.selectedTypes

/-- FixedOutput's default finalize_fixed body: initialize once, call the
original complete-Result finalize_into callback once, return its output. -/
def reference {D Out : Type} (initial : Result Out) (finish : D → Out → Result Out)
    (self : D) : Result Out := do
  let out ← initial
  finish self out

def forwarding {D Out : Type} (finalizeFixed : D → Result Out) (self : D) : Result Out :=
  finalizeFixed self

theorem complete {D Out : Type} (initial : Result Out) (finish : D → Out → Result Out)
    (self : D) :
    forwarding (fun d => do let out ← initial;finish d out) self=
      reference initial finish self := rfl

def dispatch {D N A : Type} (finish : D → GenericArray U8 N A → Result (GenericArray U8 N A))
    (fallback : D → Result (GenericArray U8 N A)) (self : D) : Result (GenericArray U8 N A) := by
  classical
  by_cases h : A=Storage U8 5
  · subst A
    exact reference (ok ⟨PV_DL_StorageBuild.build 5 (fun _ => 0#u8)⟩) finish self
  · exact fallback self

theorem dispatch_source {D N : Type}
    (finish : D → GenericArray U8 N (Storage U8 5) → Result (GenericArray U8 N (Storage U8 5)))
    (fallback : D → Result (GenericArray U8 N (Storage U8 5))) (self : D) :
    dispatch finish fallback self=
      reference (ok ⟨PV_DL_StorageBuild.build 5 (fun _ => 0#u8)⟩) finish self := by
  classical
  simp only [dispatch]
  exact dif_pos True.intro

def finisher (base : ExternalTypes) {D N A : Type}
    (fi : @digest.FixedOutput (Types base) D N A) :
    D → GenericArray U8 N A → Result (GenericArray U8 N A) :=
  @digest.FixedOutput.finalize_into (Types base) D N A fi

@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns (Types base) :=
  letI : ExternalTypes := Types base
  {ops with op212 := fun fi dc up marker => dispatch fi.finalize_into (ops.op212 fi dc up marker)}

theorem selected_native (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    {D N : Type} (fi : @digest.FixedOutput (Types base) D N (Storage U8 5))
    (dc : core.default.Default D) (up : digest.Update D) (marker : digest.digest.HashMarker D)
    (self : D) :
    @ExternalFuns.op212 (Types base) (selected base ops) D N (Storage U8 5) fi dc up marker self=
      reference (ok ⟨PV_DL_StorageBuild.build 5 (fun _ => 0#u8)⟩) (finisher base fi) self :=
  dispatch_source (finisher base fi)
    (@ExternalFuns.op212 (Types base) ops D N (Storage U8 5) fi dc up marker) self

theorem nonvacuous :
    reference (ok (0 : Nat)) (fun (_ : Unit) out => ok out) ()=ok 0 := rfl

#print axioms reference
#print axioms forwarding
#print axioms complete
#print axioms dispatch
#print axioms dispatch_source
#print axioms finisher
#print axioms selected
#print axioms selected_native
#print axioms nonvacuous
end R1Z.PV_DL_DigestFinal
