import DrvC_FirstProgram
import DrvC_SecondProgram
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_PairProgram
open Aeneas Aeneas.Std Result
open DrvC_Installation DrvC_OraclePort DrvC_Program
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def source {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) : Program Bytes State Bool :=
  bind (GExp_Experiment.first
    (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std hashv (currentDigest c)
    ⟨AspisS6CurrentVerifierCarrier.toPublic semantic,pub,proof,10#usize⟩) fun first =>
    match first with
    | .ok (.Ok saved) => bind
        (GExp_Experiment.second (stage c) c.reserved hashv (digest c) ⟨pub,proof,saved.deref⟩)
        (fun second => .done (Port1_Driver.verdict second))
    | _ => .done false

theorem bind_mapR {A B D : Type} (f : A → B) (p : Port A)
    (k : Result B → Program Bytes State D) :
    bind (mapR f p) k = bind p (fun r => k (mapResult f r)) := by
  simp only [mapR,mapProgram,DrvC_OraclePort.bind_assoc]
  rfl

/-- The headline's constructed driver and the installed two-call source share
one oracle program, including every rejected prefix and saved checkpoint. -/
theorem stages {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) :
    let r := DrvC_FirstConstants.configuration c
    Port1_Driver.stages (DrvC_Implementation.implementation r) (digest r) () semantic pub proof =
      source r hashv semantic pub proof := by
  dsimp only
  unfold Port1_Driver.stages
  rw [DrvC_FirstProgram.interpreted c hashv,bind_mapR]
  unfold source
  congr 1
  funext first
  cases first with
  | fail e => rfl
  | div => rfl
  | ok reply => cases reply with
    | Err e => rfl
    | Ok saved =>
      simp only [DrvC_Program.mapResult,DrvC_Dictionary.reply,id_eq]
      rw [DrvC_SecondProgram.program _ hashv]

#print axioms bind_mapR
#print axioms stages
end AspisR1.DrvC_PairProgram
end
