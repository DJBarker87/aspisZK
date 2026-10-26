import ARS_ReachedNumeric
import F3T_Prefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_StartCharge
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment F3T_Experiment F3T_ByteCarrier

/-- The security model extracts the FIRST submitted transcript. TX2 is its
continuation, not another independently charged transcript experiment. -/
theorem first_starts {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (a : Adversary A) (Q0 : Nat)
    (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0) (H : Bytes → State) :
    DecodedFirstReadUnionBound.decoderFirstReads RecordedBinaryExperimentBin.dec FS.emptyTable
      (eval H (F3T_Charged.charged D (F3T_Canon.canon (lift c (submission a))))).1 ≤ Q0+34 := by
  apply F3T_Charged.starts
  apply F3T_Canon.bound
  intro K
  rw [lift_eval,submission_eval]
  exact prefixBound K

/-- Q1 charges adaptive choice work in the account collision term. It does
not require a second sampler-start allowance for the same first transcript. -/
theorem total_starts {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (a : Adversary A) (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0) (H : Bytes → State) :
    DecodedFirstReadUnionBound.decoderFirstReads RecordedBinaryExperimentBin.dec FS.emptyTable
      (eval H (F3T_Charged.charged D (F3T_Canon.canon (lift c (submission a))))).1 ≤ Q0+Q1+34 := by
  exact (first_starts c D a Q0 prefixBound H).trans (by omega)

/-- Exact one-submission union-bound term, before the harmless Q0+Q1 lift. -/
theorem mass {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (a : Adversary A) (Q0 : Nat)
    (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0) :
    FS.lazyMean
      (F3T_Charged.projected D (F3T_Canon.canon (lift c (submission a)))) FS.emptyTable
      (fun run => AspisV8R19.CausalFirstHitUnionBound.indicator
        (F3T_Causal.prefixHit D (lift c (submission a)) run)) ≤
      ((Q0+34 : Nat) : Rat)*PerAttemptEnvelope.B := by
  apply F3T_Probability.restricted_union_bound
  intro K
  rw [lift_eval,submission_eval]
  exact prefixBound K

#print axioms first_starts
#print axioms total_starts
#print axioms mass
end AspisR1.ART_StartCharge
end
