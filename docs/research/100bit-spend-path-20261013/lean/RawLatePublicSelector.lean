import RawPublicOpeningWalk
import R1JointContextSound

/-! Public-free selector for a later ordinary row. It parses the current
absorb, rewinds the fixed query lookback, parses the query absorb, then applies
the public-independent opening walk to that preceding state. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawLatePublicSelector

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {M Cv W : Type} {L : Nat}

def select (p : Params M Cv L) (T : Table (Addr L) State) (tag : Byte)
    (openingFuel : Nat) (c : Addr L) : Option (UnifiedSampler.Public L) :=
  (parseAbsorb c).bind fun (endpoint, _, _) =>
  (DuplexSeek.seek p T 9 endpoint).bind fun (queryAddress, _) =>
  (parseAbsorb queryAddress).bind fun (openingEndpoint, _, _) =>
  RawPublicOpeningWalk.select p T tag openingFuel openingEndpoint

theorem select_of_joint_context (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (semanticFuel openingFuel : Nat) (c : Addr L) (T : Table (Addr L) State)
    (ctx : JointContext.Context M L) (pub : UnifiedSampler.Public L)
    (hctx : JointContext.parse p pubBytes tag semanticFuel openingFuel c T = some ctx)
    (hselected : ∀ previous ql qd,
      parseAbsorb ctx.queryAddress = some (previous, ql, qd) →
      RawPublicOpeningWalk.select p T tag openingFuel previous = some pub) :
    select p T tag openingFuel c = some pub := by
  obtain ⟨previous, ql, qd, nl, nd, xs, hc, hs, ha, _ht, _hq, _hn⟩ :=
    JointContextSound.canonical_messages p pubBytes tag semanticFuel openingFuel c T ctx hctx
  simp [select, hc, hs, ha, hselected previous ql qd ha]

#print axioms select_of_joint_context
end AspisR1.RawLatePublicSelector
end
