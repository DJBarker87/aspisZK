import AuS1_Context
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Bound
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound

def loss (Q : Nat) : Rat := 6 * ((Q + 1040 : Nat) : Rat)^2 / (256^32 : Rat)

/-- Existing probability law, with ALL1040 replay queries charged once.
GExp owns the concrete whole-experiment source and its uniform budget. -/
 theorem collision_loss {A : Type} (source : Program Bytes State A)
    (prepare : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) (Q : Nat)
    (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q) :
    lazyMean (SdkC_Replay.augmented source prepare) emptyTable
      (fun view => indicator (BinRawByteCollisionTargets.event
        SelectedTranscriptParams.params.iv (Q+1040) view)) ≤ loss Q :=
  SdkC_Replay.collision_bound source prepare Q budget

 theorem loss_binary (Q : Nat) : loss Q = 6 * ((Q + 1040 : Nat) : Rat)^2 / (2^256 : Rat) := by
  have power : (256^32 : Rat) = 2^256 := by
    calc
      (256^32 : Rat) = ((2^8)^32 : Rat) := rfl
      _ = (2^(8*32) : Rat) := (pow_mul 2 8 32).symm
      _ = (2^256 : Rat) := rfl
  unfold loss
  rw [power]

#print axioms collision_loss
#print axioms loss_binary
end AspisR1.AuS1_Bound
end
