import BinRawByteCollisionTargets

/-! Binary instantiation of the arity-generic AllAddressCollision.mass.
Same unrestricted-byte event shape consumed by RawAdaptiveDecoderInjection's
kappa interface, with five readers instead of eleven. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.BinCombinedMerkleCollision
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound

abbrev Coll {O : Type} (iv : State) (Q : Nat) (v : View Bytes State O) : Prop :=
  BinRawByteCollisionTargets.event iv Q v

def kappa (Q : Nat) : ℚ := 6 * (Q : ℚ)^2 / (256^32 : ℚ)
abbrev budget := kappa

theorem target_count : Fintype.card (Fin 5) = 5 := Fintype.card_fin 5

theorem mass {O : Type} (iv : State) (Q : Nat) (p : Program Bytes State O)
    (hQ : ∀ H : Bytes → State, firstReads emptyTable (eval H p).1 ≤ Q) :
    lazyMean p emptyTable (fun v => indicator (Coll iv Q v)) ≤ kappa Q :=
  BinRawByteCollisionTargets.mass iv Q p hQ

#print axioms target_count
#print axioms mass
end AspisR1.BinCombinedMerkleCollision
end
