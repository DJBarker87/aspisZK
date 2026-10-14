import R1JointContextSound
import R1JointPrefixAnswers

/-! Once the joint public context parses, the endpoint seek remains available
for every completion of the missing table answers. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.JointRecoveryTotal

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem recover_of_seek (p : Params M Cv L) (T : Table (Addr L) State)
    (acc : Addr L → State) (endpoint : State) (a : Addr L) (xs : List State)
    (hs : DuplexSeek.seek p T 9 endpoint = some (a, xs)) :
    QueryDecoder.recover p T acc endpoint =
      some (a, QueryCompletion.complete p T acc xs) := by
  unfold QueryDecoder.recover
  rw [hs]
  rfl

theorem parse_recover (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (semanticFuel openingFuel : Nat) (c : Addr L) (T : Table (Addr L) State)
    (ctx : JointContext.Context M L)
    (hparse : JointContext.parse p pubBytes tag semanticFuel openingFuel c T =
      some ctx) :
    ∃ xs, ∀ acc : Addr L → State,
      QueryDecoder.recover p T acc ctx.endpoint =
        some (ctx.queryAddress, QueryCompletion.complete p T acc xs) := by
  obtain ⟨_, _, _, _, _, xs, _, hseek, _, _, _, _⟩ :=
    JointContextSound.parse_sound p pubBytes tag semanticFuel openingFuel c T ctx hparse
  exact ⟨xs, fun acc => recover_of_seek p T acc ctx.endpoint ctx.queryAddress xs hseek⟩

theorem fromAnswers_has_query (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (semanticFuel openingFuel : Nat) (c : Addr L) (T : Table (Addr L) State)
    (ctx : JointContext.Context M L)
    (hparse : JointContext.parse p pubBytes tag semanticFuel openingFuel c T =
      some ctx) (as : List State) :
    ∃ qr, (JointPrefixAnswers.fromAnswers p T ctx.records ctx.endpoint as).2 =
      some (ctx.queryAddress, qr) := by
  obtain ⟨xs, hrecover⟩ := parse_recover p pubBytes tag semanticFuel openingFuel c T ctx hparse
  let acc := R0C.V3.DQ.accFrom (JointPrefixAnswers.missing p T ctx.records ctx.endpoint) as
  refine ⟨QueryCompletion.complete p T acc xs, ?_⟩
  change QueryDecoder.recover p T acc ctx.endpoint =
    some (ctx.queryAddress, QueryCompletion.complete p T acc xs)
  exact hrecover acc

#print axioms recover_of_seek
#print axioms parse_recover
#print axioms fromAnswers_has_query

end AspisR1.JointRecoveryTotal
end
