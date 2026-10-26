import SCH_AccountCuts
import SCG_AcceptedPair
import SCE_FirstCutBytes
import SCE_Projection
import CPH_Game
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARP_Interface
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment SCE_Execution S2W_NativeConsolidation

variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

/-- The account interface which is available WITHOUT a bank-support promise.
The actual first reply selects the second entry and both ideal source cuts.
The log retains both adversarial choices, including duplicate queries. -/
theorem accepted_cuts (a : Adversary A) :
    ∀ H : Bytes → State,
    accepted (eval H (account c hashv copy allocator id a)).2 = true →
    ∃ saved post final f s,
      (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 =
        ok (.Ok (saved,post,final)) ∧
      SourceCuts (SCH_IdealSdk.dictionary c hashv H) (eval H a.first).2.entry.first
        ((eval H (a.second (eval H a.first).2 saved post final)).2.entry.second secondSizes)
        saved f s ∧
      (eval H (submission a)).2 =
        (⟨MultiproofConeCanonical.bytesOf f.pub.val,
          MultiproofConeCanonical.bytesOf f.proof.val⟩ : F3T_ByteCarrier.Submission) ∧
      (eval H (account c hashv copy allocator id a)).1 =
        (eval H a.first).1 ++
          ((eval H (firstCode c hashv copy allocator id (eval H a.first).2)).1 ++
          ((eval H (a.second (eval H a.first).2 saved post final)).1 ++
          (eval H (secondCode c hashv allocator id
            (eval H (a.second (eval H a.first).2 saved post final)).2)).1)) := by
  intro H success
  obtain ⟨saved,post,final,post2,final2,first,second⟩ :=
    SCG_AcceptedPair.replies c hashv copy allocator id a H success
  obtain ⟨f,s,cuts⟩ := SCH_SourceCuts.pair _ id _ _ _ _ _ saved
    (SCH_SourceFirst.accepted c hashv copy allocator id _ saved post final H first)
    (SCH_SourceSecond.accepted c hashv allocator id _ post2 final2 H second)
  refine ⟨saved,post,final,f,s,first,cuts,?_,?_⟩
  · rw [submission_eval]
    have bytes := SCE_FirstCutBytes.submitted_cut (eval H a.first).2 _ _ saved f s cuts
    exact SCE_SubmissionExt.equal _ _ bytes.1 bytes.2
  · exact congrArg Prod.fst (accepted_eval c hashv copy allocator id a H saved post final first)

/-- Diagnostic obligation, not a trust item and not an assumption installed
in a replacement top. A fixed game at the root's H does not prove this.
It indexes the four approved game fields by the actual first reply in EVERY H.
No filtering or conditioning of account outcomes is performed. -/
def BankSupported {Tx : Type} (a : Adversary A)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (system : S2W_ExtractionBoundary.Program) : Prop :=
  ∀ (H : Bytes → State) saved post final,
    accepted (eval H (account c hashv copy allocator id a)).2 = true →
    (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 =
      ok (.Ok (saved,post,final)) →
    ∃ (p : CPG_Projection.Observations Tx A) (t u : Tx) (actions : List (CPP_BankState.Action A)),
      CPH_Game.DeployedPairExecution p t u (eval H a.first).2.entry
        (eval H (a.second (eval H a.first).2 saved post final)).2.entry
        saved actions n1 n2 copy allocator id ∧
      CPR_DataPersistence.TwoTransactionLaw
        (CPG_Projection.adjacent p) (CPG_Projection.ordinary p system)
        (CPG_Projection.before p) (CPG_Projection.tentative p)
        (CPG_Projection.success p) (CPG_Projection.loaded p)

/-- Exact observation of the original account. Applying ANY log/outcome
functional gives the original value; in particular costs and per-world event
indicators are not changed. This covers the SCE image only, not arbitrary
independent P/runtime inputs of Rc9. -/
theorem representation (a : Adversary A) (H : Bytes → State) :
    eval H (runtime c hashv copy allocator id a) =
      let v := eval H (account c hashv copy allocator id a)
      (v.1,some (v.1,(F3T_Canon.canonInput
        (F3T_ByteCarrier.input c (submitted v.2.1)),accepted v.2))) :=
  runtime_eval c hashv copy allocator id a H

#print axioms accepted_cuts
#print axioms representation
#print BankSupported
end AspisR1.ARP_Interface
end
