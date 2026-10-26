import SCJ_Domination
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCJ_Composition
open FS FS2 FS2.Duplex
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_ByteCarrier OraclePortRefineJoin

theorem account_of_branch {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : SCE_Experiment.Adversary A) (H : Bytes → State) (run : RunView)
    (observed : (eval H (SCE_Experiment.runtime c hashv copy allocator id a)).2 = some run)
    (success : run.2.2 = true)
    (sourceSuccess : (eval H (F3T_Installed.source c hashv
      (input c (eval H (SCE_Experiment.submission a)).2))).2 = true)
    (projected full : Prop)
    (rawOr : eval H (F3T_Installed.source c hashv
      (input c (eval H (SCE_Experiment.submission a)).2)) =
      eval H (F3_Model.verifier D (input c (eval H (SCE_Experiment.submission a)).2)) ∨ projected)
    (transport : projected → full) (clean : ¬ full)
    (ordered : (eval H (SCE_Experiment.account c hashv copy allocator id a)).1 =
      (eval H a.first).1 ++ (eval H (F3T_Installed.source c hashv
        (input c (eval H (SCE_Experiment.submission a)).2))).1) :
    (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift c (SCE_Experiment.submission a))))).2.2 = true ∧
    RecoveredInputAgreement (view run)
      (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift c (SCE_Experiment.submission a))))) := by
  have raw : eval H (F3T_Installed.source c hashv
      (input c (eval H (SCE_Experiment.submission a)).2)) =
      eval H (F3_Model.verifier D (input c (eval H (SCE_Experiment.submission a)).2)) :=
    rawOr.resolve_right (fun hit => clean (transport hit))
  exact SCI_Recovery.account_of_join c D hashv copy allocator id a H run observed
    success sourceSuccess raw ordered

#print axioms account_of_branch
end AspisR1.SCJ_Composition
end
