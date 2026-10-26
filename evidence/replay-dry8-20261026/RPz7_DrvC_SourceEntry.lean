import RPz7_DrvC_PairProgram
import RPz7_DrvC_Headline
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_SourceEntry
open Aeneas Aeneas.Std Result
open DrvC_Installation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open OraclePortRuntimeBindingC7

/-- Literal installed decoder/validator followed by the two source effect
programs; the source obtains its TX2 checkpoint from this TX1 reply. -/
def source {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) : Verifier := fun i =>
  match Port1_Driver.asSlice i.statement.pubBytes, Port1_Driver.asSlice i.stored with
  | some pub, some proof =>
    match Port1_Driver.decodeSemantic (sdk c) pub with
    | .ok (some semantic) => DrvC_PairProgram.source c hashv semantic pub proof
    | _ => .done false
  | _, _ => .done false

/-- Equality of complete oracle programs on every physical byte input.
No input equality, accepted trace or compatibility certificate is assumed. -/
theorem same_program {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) :
    DrvC_Implementation.driver (DrvC_FirstConstants.configuration c) =
      source (DrvC_FirstConstants.configuration c) hashv := by
  funext i
  unfold DrvC_Implementation.driver Port1_Driver.rust source
  cases hp : Port1_Driver.asSlice i.statement.pubBytes with
  | none => rfl
  | some pub =>
    cases hs : Port1_Driver.asSlice i.stored with
    | none => rfl
    | some proof =>
      dsimp only
      cases hd : Port1_Driver.decodeSemantic (sdk (DrvC_FirstConstants.configuration c)) pub with
      | fail e => rfl
      | div => rfl
      | ok semantic => cases semantic with
        | none => rfl
        | some semantic => exact DrvC_PairProgram.stages c hashv semantic pub proof

theorem physical {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) :
    Port1_StoredCarrier.Physical (source (DrvC_FirstConstants.configuration c) hashv) := by
  rw [← same_program c hashv]
  exact DrvC_Implementation.physical _

theorem aus1_dictionary {F C : Type} (c : Configuration F C) :
    let r := DrvC_FirstConstants.configuration c
    sdk r = SdkD_PairBatches.dictionary r.adapter r.currentBase r.stageBase r.finish
      r.reserved r.query r.geometry r.boundaries r.std := DrvC_Installation.aus1_dictionary _

#print axioms same_program
#print axioms physical
#print axioms aus1_dictionary
#print same_program
end AspisR1.DrvC_SourceEntry
end
