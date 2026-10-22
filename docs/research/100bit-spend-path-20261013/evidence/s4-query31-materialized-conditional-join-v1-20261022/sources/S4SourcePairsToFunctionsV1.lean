import Query31SourceOracleBridge
import Query31MathematicalSchedule
import S4QueryArrayViewsV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section

namespace AspisR1.S4SourcePairsToFunctionsV1
open AspisR1PublicPreparation
open AspisR1PublicPreparation.Query31SourceSchedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep FS2.Duplex
open AspisV8R19.SqueezeOracleBridge

def sourcePairBlocks {H : Type} {D : aspis_core.Digest32 H} {hash : H}
    (pairs : List (DigestPair D hash)) (fallback : TranscriptStep.Bytes32) : Nat → TranscriptStep.Bytes32 :=
  fun k => ((pairs[k]?.map (fun pair => pair.squeeze.output)).getD fallback)

def sourcePairStates {H : Type} {D : aspis_core.Digest32 H} {hash : H}
    (pairs : List (DigestPair D hash)) (initial : TranscriptStep.Bytes32) : Nat → TranscriptStep.Bytes32
  | 0 => initial
  | k + 1 => ((pairs[k]?.map (fun pair => pair.advance.output)).getD initial)

private theorem stateChain_adjacent_get {H : Type} {D : aspis_core.Digest32 H} {hash : H}
    (pairs : List (DigestPair D hash)) (hchain : stateChain pairs)
    (k : Nat) (hk : k + 1 < pairs.length) :
    pairs[k+1]?.map (fun pair => pair.state) =
      pairs[k]?.map (fun pair => pair.advance.output) := by
  induction pairs generalizing k with
  | nil => simp at hk
  | cons first rest ih =>
      cases rest with
      | nil => simp at hk
      | cons second tail =>
          cases k with
          | zero =>
              change second.state = first.advance.output ∧ stateChain (second :: tail) at hchain
              simpa using hchain.1
          | succ k =>
              change second.state = first.advance.output ∧ stateChain (second :: tail) at hchain
              have htail : k + 1 < (second :: tail).length := by simp at hk ⊢; omega
              have h := ih hchain.2 k htail
              simpa using h

private theorem sourcePairState_eq_pair {H : Type} {D : aspis_core.Digest32 H} {hash : H}
    (pairs : List (DigestPair D hash)) (initial : TranscriptStep.Bytes32)
    (hfirst : ∃ first rest, pairs = first :: rest ∧ first.state = initial)
    (hchain : stateChain pairs) {k : Nat} (hk : k < pairs.length) :
    sourcePairStates pairs initial k = pairs[k].state := by
  induction k with
  | zero =>
      rcases hfirst with ⟨first,rest,rfl,hstate⟩
      simpa [sourcePairStates, hstate]
  | succ k ih =>
      have hkprev : k + 1 < pairs.length := hk
      have hadj := stateChain_adjacent_get pairs hchain k hkprev
      have hraw : pairs[k+1]? = some pairs[k+1] :=
        List.getElem?_eq_some_iff.mpr ⟨hk, rfl⟩
      have hget : pairs[k+1]?.map (fun pair => pair.state) =
          some pairs[k+1].state := by simpa using congrArg (Option.map (fun pair => pair.state)) hraw
      have hget' : pairs[k]?.map (fun pair => pair.advance.output) =
          some pairs[k+1].state := hadj.symm.trans hget
      simp only [sourcePairStates, hget']
      rfl

private theorem sourcePairBlock_eq_pair {H : Type} {D : aspis_core.Digest32 H} {hash : H}
    (pairs : List (DigestPair D hash)) (fallback : TranscriptStep.Bytes32)
    {k : Nat} (hk : k < pairs.length) :
    sourcePairBlocks pairs fallback k = pairs[k].squeeze.output := by
  have hraw : pairs[k]? = some pairs[k] :=
    List.getElem?_eq_some_iff.mpr ⟨hk, rfl⟩
  have hget : pairs[k]?.map (fun pair => pair.squeeze.output) =
      some pairs[k].squeeze.output := by simpa using congrArg (Option.map (fun pair => pair.squeeze.output)) hraw
  simp [sourcePairBlocks, hget]

/-- The functions fed to the literal query-prefix model can be built directly
from the same emitted digest-pair list. The adjacent-state invariant supplies
the carry between a pair's advance output and the next pair's input. -/
theorem sourcePair_functions_of_chain {H : Type} {D : aspis_core.Digest32 H} {hash : H}
    (absorbed : transcript.Transcript H) (pairs : List (DigestPair D absorbed.hash))
    (hlen : pairs.length = 8)
    (hfirst : ∃ first rest, pairs = first :: rest ∧ first.state = absorbed.state)
    (hchain : stateChain pairs) :
    sourcePairStates pairs absorbed.state 0 = absorbed.state ∧
    (∀ k < 8,
      D.digest absorbed.hash (TranscriptStep.readParts (sourcePairStates pairs absorbed.state k) 2#u8) =
        ok (sourcePairStates pairs absorbed.state (k+1))) ∧
    (∀ k < 8,
      D.digest absorbed.hash (TranscriptStep.readParts (sourcePairStates pairs absorbed.state k) 1#u8) =
        ok (sourcePairBlocks pairs absorbed.state k)) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro k hk
    have hkpair : k < pairs.length := by rw [hlen]; exact hk
    let pair := pairs[k]'hkpair
    have hstate := sourcePairState_eq_pair pairs absorbed.state hfirst hchain hkpair
    have hnext : sourcePairStates pairs absorbed.state (k+1) = pair.advance.output := by
      have hraw : pairs[k]? = some pair := by
        dsimp [pair]
        exact List.getElem?_eq_some_iff.mpr ⟨hkpair, rfl⟩
      have hget : pairs[k]?.map (fun pair => pair.advance.output) =
          some pair.advance.output := by simpa using congrArg (Option.map (fun pair => pair.advance.output)) hraw
      simp [sourcePairStates, pair, hget]
    have hcall : D.digest absorbed.hash (TranscriptStep.readParts pair.state 2#u8) =
        ok pair.advance.output := by
      rw [← pair.hadvanceState, ← pair.hadvanceTag, ← digestCall_input_eq_readParts]
      exact pair.advance.hdigest
    simpa [hstate, hnext] using hcall
  · intro k hk
    have hkpair : k < pairs.length := by rw [hlen]; exact hk
    let pair := pairs[k]'hkpair
    have hstate := sourcePairState_eq_pair pairs absorbed.state hfirst hchain hkpair
    have hblock := sourcePairBlock_eq_pair pairs absorbed.state hkpair
    have hcall : D.digest absorbed.hash (TranscriptStep.readParts pair.state 1#u8) =
        ok pair.squeeze.output := by
      rw [← pair.hsqueezeState, ← pair.hsqueezeTag, ← digestCall_input_eq_readParts]
      exact pair.squeeze.hdigest
    simpa [hstate, hblock] using hcall

#print axioms sourcePair_functions_of_chain
end AspisR1.S4SourcePairsToFunctionsV1
end
