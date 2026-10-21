import OraclePortRowAwareCausalD1
import OraclePortCompletionDraft

/-! Exact conditional completion transport and unchanged binary mass.
GateAtRows remains an explicit obligation; it is not a premise deletion. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortRowAwareTransportD7
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open OraclePortExperiment
open RawCutProverCompiler (Prover RunView)
open OraclePortRowAwareCausalD1
abbrev collision := RecordedBinaryExperimentBin.binaryCollision

def Completion (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover)
    (Q : Nat) : Prop :=
  ∀ H : Bytes → State, ¬ collision Q (eval H (recorded D dO P)) →
    FS2.accepts (eval H (recorded D dO P)) →
    ∀ n a, n < (LiteralByteProtocol.protocol D).r →
      firstCell ((LiteralByteProtocol.protocol D).chain H
        (eval H (recorded D dO P)).2.1.1 (eval H (recorded D dO P)).2.1.2 n) = some a →
      ∃ own pend g, (decode D) a (tableBefore emptyTable (eval H (recorded D dO P)).1 a) =
        some (own, pend, g) ∧
        bfollow g (traceFrom (eval H (recorded D dO P)).1 a) own pend
          (tableBefore emptyTable (eval H (recorded D dO P)).1 a) =
        some ((LiteralByteProtocol.protocol D).transcript H
            (eval H (recorded D dO P)).2.1.1 (eval H (recorded D dO P)).2.1.2 n,
          (LiteralByteProtocol.protocol D).msg (eval H (recorded D dO P)).2.1.2 n,
          (LiteralByteProtocol.protocol D).chal H
            (eval H (recorded D dO P)).2.1.1 (eval H (recorded D dO P)).2.1.2 n)

def GateAtRows (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover)
    (Q : Nat) : Prop :=
  ∀ H : Bytes → State, ¬ collision Q (eval H (recorded D dO P)) →
    FS2.accepts (eval H (recorded D dO P)) →
    ∀ n a, n < (LiteralByteProtocol.protocol D).r →
      firstCell ((LiteralByteProtocol.protocol D).chain H
        (eval H (recorded D dO P)).2.1.1 (eval H (recorded D dO P)).2.1.2 n) = some a →
      Gate D a (tableBefore emptyTable (eval H (recorded D dO P)).1 a)

theorem completion_transport (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (P : Prover) (Q : Nat) (hc : OraclePortConsumer.Completion D dO P Q)
    (hg : GateAtRows D dO P Q) : Completion D dO P Q := by
  intro H hout ha n a hn hf
  obtain ⟨own,pend,g,hd,hfollow⟩ := hc H hout ha n a hn hf
  refine ⟨own,pend,g,?_,hfollow⟩
  rw [decode_of_gate D a _ (hg H hout ha n a hn hf)]
  exact hd

theorem completion_of_checks (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (P : Prover) (Q : Nat)
    (hQ : ∀ H, firstReads emptyTable (eval H (original D dO P)).1 ≤ Q)
    (checks : OraclePortConsumer.CheckedAcceptance D dO P Q)
    (tag : ∀ H, FS2.accepts (eval H (original D dO P)) →
      (eval H (original D dO P)).2.1.1.tag = 2)
    (hg : GateAtRows D dO P Q) : Completion D dO P Q :=
  completion_transport D dO P Q
    (OraclePortCompletionDraft.completion_of_checks D dO P Q hQ checks tag) hg

theorem classifier_density (D : LiteralByteProtocol.Decoder)
    (a : Bytes) (T : Table Bytes State) own pend g
    (hd : decode D a T = some (own,pend,g)) :
    blaw g (fun out => indicator (RawAdaptiveClassifierHitDensity.classifier
      out.1 out.2.1 T out.2.2)) own pend ≤ PerAttemptEnvelope.B :=
  RawAdaptiveClassifierHitDensity.adaptive_decoded_classifier_le
    RawFullPublicSelection.select LiteralTableWordChoiceBin.choose a T own pend g
    ((decode_some D a T own pend g).mp hd).2

theorem decoded_union_bound {Pf : Type} (D : LiteralByteProtocol.Decoder)
    (exp : Program Bytes State (Pf × Bool)) (N : Nat)
    (hN : DecodedFirstReadUnionBound.DecoderReadsBound (decode D) exp emptyTable N) :
    lazyMean exp emptyTable (fun v => indicator
      (hitsChain3 (decode D) RawAdaptiveClassifierHitDensity.classifier emptyTable v.1)) ≤
      (N : ℚ) * PerAttemptEnvelope.B := by
  apply DecodedFirstReadUnionBound.decoded_first_read_bound (decode D)
    RawAdaptiveClassifierHitDensity.classifier PerAttemptEnvelope.B exp emptyTable N
  · unfold PerAttemptEnvelope.B; positivity
  · exact classifier_density D
  · exact hN

theorem binary_mass_unchanged {O : Type} (iv : State) (Q : Nat)
    (exp : Program Bytes State O)
    (hQ : ∀ H, firstReads emptyTable (eval H exp).1 ≤ Q) :
    lazyMean exp emptyTable (fun v => indicator (BinCombinedMerkleCollision.Coll iv Q v)) ≤
      BinCombinedMerkleCollision.kappa Q :=
  BinCombinedMerkleCollision.mass iv Q exp hQ

#print axioms completion_transport
#print axioms completion_of_checks
#print axioms classifier_density
#print axioms decoded_union_bound
#print axioms binary_mass_unchanged
end AspisR1.OraclePortRowAwareTransportD7
end
