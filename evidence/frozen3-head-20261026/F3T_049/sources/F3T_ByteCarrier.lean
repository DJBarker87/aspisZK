import F3T_Installed
import F3J_Public
import Port1_CanonicalJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_ByteCarrier
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1CurrentCaller
open F3T_Experiment
abbrev Submission := Port1_StoredCarrier.Submission
abbrev ByteProver := Port1_StoredCarrier.ByteProver

/-- Total bounded semantic output. Failure branches remain explicit and do
not assert that accepted source inputs take them. -/
def publicOf (b : Bytes) : LiteralTranscript.Public :=
  if fit : 75+b.length≤SelectedTranscriptParams.L then ⟨b,fit,2⟩
  else ⟨[],by decide,2⟩

def semantic {F C : Type} (c : DrvC_Installation.Configuration F C) (s : Submission) :
    LiteralTranscript.Public :=
  match Port1_Driver.asSlice s.publicBytes with
  | none => publicOf []
  | some pub => match Port1_Driver.decodeSemantic (DrvC_Installation.sdk c) pub with
    | .ok (some v) => match AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic v)) with
      | .ok (.Ok encoded) => publicOf (MultiproofConeCanonical.bytesOf encoded.val)
      | _ => publicOf []
    | _ => publicOf []

def input {F C : Type} (c : DrvC_Installation.Configuration F C) (s : Submission) : F3_Model.Input :=
  ⟨⟨semantic c s⟩,⟨s.publicBytes⟩,Port1_StoredCarrier.proof s.stored,s.stored⟩

def lift {F C : Type} (c : DrvC_Installation.Configuration F C) (P : ByteProver) : Prover :=
  bind P fun s => .done (input c s)

theorem lift_eval {F C : Type} (c : DrvC_Installation.Configuration F C)
    (P : ByteProver) (H : Bytes → State) :
    eval H (lift c P)=((eval H P).1,input c (eval H P).2) := by
  simp only [lift,eval_bind,eval,List.append_nil]

theorem public_bytes {F C : Type} (c : DrvC_Installation.Configuration F C) (s : Submission) :
    (input c s).physical.bytes=s.publicBytes := rfl

theorem stored_bytes {F C : Type} (c : DrvC_Installation.Configuration F C) (s : Submission) :
    (input c s).stored=s.stored := rfl

#print axioms lift_eval
#print axioms public_bytes
#print axioms stored_bytes
end AspisR1.F3T_ByteCarrier
end
