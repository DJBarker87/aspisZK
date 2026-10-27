import RPz7_Hist_ChargedBinding
import S2W_NativeConsolidation
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_PairExperiment
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.CausalFirstHitUnionBound AspisV8PairedCommitment
open MultiproofConeCanonical S2W_NativeConsolidation

/-- Plain returned data, containing no authentication/history law. A concrete
containing source experiment must produce these exact same-execution cuts. -/
structure Pair where
  first : FirstCut
  second : SecondCut

def select (pair : Pair) : R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
  (⟨bytesOf pair.first.proof.val,bytesOf pair.first.pub.val⟩,
   ⟨bytesOf pair.second.proof.val,bytesOf pair.second.pub.val⟩)

def charged (source : Program Bytes State Pair) : Program Bytes State Pair :=
  Hist_AuditQueries.augmented source select

theorem same_result (H : Bytes → State) (source : Program Bytes State Pair) :
    (eval H (charged source)).2 = (eval H source).2 :=
  Hist_ChargedBinding.result_preserved H source select

theorem binding_or_collision (iv : State) (source : Program Bytes State Pair)
    (Q : Nat) (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q)
    (H : Bytes → State) :
    BinRawByteCollisionTargets.event iv (Q+4) (eval H (charged source)) ∨
      S2W_AuthenticatedInputs.P2Prime H (eval H source).2.first.proof (eval H source).2.first.pub
        (eval H source).2.second.proof (eval H source).2.second.pub := by
  rcases Hist_ChargedBinding.binding_or_collision iv source select Q budget H with bad | binding
  · exact Or.inl bad
  · exact Or.inr ⟨binding⟩

theorem collision_bound (iv : State) (source : Program Bytes State Pair)
    (Q : Nat) (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q) :
    lazyMean (charged source) emptyTable
      (fun view => indicator (BinRawByteCollisionTargets.event iv (Q+4) view)) ≤
      6 * ((Q+4 : Nat) : Rat)^2 / (256^32 : Rat) :=
  Hist_ChargedBinding.collision_bound iv source select Q budget

#print axioms same_result
#print axioms binding_or_collision
#print axioms collision_bound
end AspisR1.Hist_PairExperiment
end
