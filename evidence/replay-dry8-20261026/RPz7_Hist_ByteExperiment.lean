import RPz7_Hist_PairExperiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_ByteExperiment
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8PairedCommitment
open AspisV8R19.CausalFirstHitUnionBound
open MultiproofConeCanonical S2W_NativeConsolidation
abbrev BytesPair := R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs

def charged (source : Program Bytes State BytesPair) : Program Bytes State BytesPair :=
  Hist_AuditQueries.augmented source id

theorem same_result (H : Bytes → State) (source : Program Bytes State BytesPair) :
    (eval H (charged source)).2 = (eval H source).2 :=
  Hist_ChargedBinding.result_preserved H source id

theorem binding_or_collision (iv : State) (source : Program Bytes State BytesPair)
    (Q : Nat) (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q)
    (H : Bytes → State) (f : FirstCut) (s : SecondCut)
    (associated : (eval H source).2 = Hist_PairExperiment.select ⟨f,s⟩) :
    BinRawByteCollisionTargets.event iv (Q+4) (eval H (charged source)) ∨
      S2W_AuthenticatedInputs.P2Prime H f.proof f.pub s.proof s.pub := by
  rcases Hist_ChargedBinding.binding_or_collision iv source id Q budget H with bad | binding
  · exact Or.inl bad
  · rw [associated] at binding
    exact Or.inr ⟨binding⟩

theorem collision_bound (iv : State) (source : Program Bytes State BytesPair)
    (Q : Nat) (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q) :
    lazyMean (charged source) emptyTable
      (fun view => indicator (BinRawByteCollisionTargets.event iv (Q+4) view)) ≤
      6 * ((Q+4 : Nat) : Rat)^2 / (256^32 : Rat) :=
  Hist_ChargedBinding.collision_bound iv source id Q budget

#print axioms same_result
#print axioms binding_or_collision
#print axioms collision_bound
end AspisR1.Hist_ByteExperiment
end
