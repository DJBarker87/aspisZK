import S2W_AuthenticatedInputs
import BinRawByteCollisionTargets
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_P2Prime
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.CausalFirstHitUnionBound
open AspisV8PairedCommitment

/-- Pair binding is derived on one consistent bounded log. The bad event is
explicit; no global injectivity property of SHA or H is assumed. -/
theorem binding_or_collision (iv : State) (H : Bytes → State)
    (log : List (Bytes × State)) (Q : Nat)
    (consistent : ∀ q ∈ log, q.2 = H q.1)
    (budget : firstReads emptyTable log ≤ Q)
    (written current : R9PoolRuntimeBinding.Inputs)
    (wp : Read log written.proof) (wu : Read log written.pub)
    (cp : Read log current.proof) (cu : Read log current.pub) :
    FS.hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable log ∨
      R9PoolRuntimeBinding.P2Prime H written current := by
  classical
  by_cases bad : FS.hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable log
  · exact Or.inl bad
  right
  intro matched
  constructor
  · by_contra different
    exact AllAddressCollisionTrace.outputs_injective iv BinRawByteCollisionTargets.pred H log Q
      consistent budget bad current.proof written.proof cp wp different matched.1
  · by_contra different
    exact AllAddressCollisionTrace.outputs_injective iv BinRawByteCollisionTargets.pred H log Q
      consistent budget bad current.pub written.pub cu wu different matched.2

/-- The existing binary collision event already covers both byte comparisons.
Q counts all source/adversary/verifier first reads, including failed prefixes.
The source Program is fixed before H and no replay reads are free. -/
theorem collision_bound {A : Type} (iv : State) (program : FS2.Duplex.Program Bytes State A)
    (Q : Nat) (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H program).1 ≤ Q) :
    lazyMean program emptyTable (fun view => indicator (BinRawByteCollisionTargets.event iv Q view)) ≤
      6 * (Q : Rat)^2 / (256^32 : Rat) :=
  BinRawByteCollisionTargets.mass iv Q program budget

#print axioms binding_or_collision
#print axioms collision_bound
end AspisR1.Hist_P2Prime
end
