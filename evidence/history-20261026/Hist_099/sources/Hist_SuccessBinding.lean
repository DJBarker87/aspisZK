import Hist_ByteExperiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_SuccessBinding
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8PairedCommitment

/-- Success-conditioned byte identity. Both digest comparisons are required;
no unconditional equality is inferred merely from protected checkpoint bytes.
The loss is that of Hist_ByteExperiment.collision_bound on the same Program. -/
theorem equal_or_collision (iv : State)
    (source : Program Bytes State Hist_ByteExperiment.BytesPair) (Q : Nat)
    (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q)
    (H : Bytes → State)
    (matched : R9PoolRuntimeBinding.digestMatches H (eval H source).2.1 (eval H source).2.2) :
    BinRawByteCollisionTargets.event iv (Q+4) (eval H (Hist_ByteExperiment.charged source)) ∨
      (eval H source).2.2 = (eval H source).2.1 := by
  rcases Hist_ChargedBinding.binding_or_collision iv source id Q budget H with bad | binding
  · exact Or.inl bad
  · exact Or.inr (R9PoolRuntimeBinding.accepted_same_inputs H _ _ binding matched)

/-- Any chosen success predicate may be carried through pointwise. No
conditional-probability bound or free success conditioning is asserted. -/
theorem successful_equal_or_collision (iv : State)
    (source : Program Bytes State Hist_ByteExperiment.BytesPair) (Q : Nat)
    (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q)
    (success : Hist_ByteExperiment.BytesPair → Prop)
    (successfulMatches : ∀ H : Bytes → State, success (eval H source).2 →
      R9PoolRuntimeBinding.digestMatches H (eval H source).2.1 (eval H source).2.2)
    (H : Bytes → State) (accepted : success (eval H source).2) :
    BinRawByteCollisionTargets.event iv (Q+4) (eval H (Hist_ByteExperiment.charged source)) ∨
      (eval H source).2.2 = (eval H source).2.1 :=
  equal_or_collision iv source Q budget H (successfulMatches H accepted)

#print axioms equal_or_collision
#print axioms successful_equal_or_collision
end AspisR1.Hist_SuccessBinding
end
