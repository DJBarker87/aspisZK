import AspisFormal.K1.V7Tag73ExactCompilerGammaPrefixCoordinates

/-!
# Fuel-free lookup digest chains

This module records the literal state-changing table lookups of a successful
evaluator run without imposing scheduler chronology.  It is deliberately
lower-level than `V7Tag73ExactRootCausalChain`: a consumed duplex chain already
contains every advance lookup, so extending a lookup chain needs neither a
root-order proof nor transition-fuel room.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PureLookupDigestChain

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

/-- A lookup-only causal chain.  Every state-changing input literally starts
with the preceding digest; no chronology or first-exposure fact is asserted. -/
inductive PureLookupDigestChain
    (table : FixedOracleTable) (boundaryInput : ShaInput)
    (allowedInput : ShaInput → Prop) : Digest256 → Digest256 → Prop
  | boundary (initial : Digest256)
      (lookup : tableLookup table boundaryInput = some initial) :
      PureLookupDigestChain table boundaryInput allowedInput initial initial
  | step (initial current next : Digest256) (input : ShaInput)
      (chain : PureLookupDigestChain table boundaryInput allowedInput initial
        current)
      (causalPrefix : bytes current = input.take 32)
      (allowed : allowedInput input)
      (lookup : tableLookup table input = some next) :
      PureLookupDigestChain table boundaryInput allowedInput initial next

theorem pure_lookup_digest_chain_terminal_lookup
    {table : FixedOracleTable} {boundaryInput : ShaInput}
    {allowedInput : ShaInput → Prop} {initial terminal : Digest256}
    (chain : PureLookupDigestChain table boundaryInput allowedInput initial
      terminal) :
    ∃ input, tableLookup table input = some terminal := by
  cases chain with
  | boundary lookup => exact ⟨boundaryInput, lookup⟩
  | step current next input previous causalPrefix allowed lookup =>
      exact ⟨input, lookup⟩

/-- State-changing inputs allowed after an absorption boundary. -/
def IsPurePostRootStateInput (forbiddenLabel : UInt8)
    (input : ShaInput) : Prop :=
  (∃ state : Digest256, input = gammaAdvanceInput state) ∨
    ∃ (state : Digest256) (payload : Payload),
      payload.label ≠ forbiddenLabel ∧
      input = bytes state ++ [domAbsorb, payload.label] ++ payload.data

/-- Matching event-local grammar condition. -/
def IsPurePostRootMachineEvent (forbiddenLabel : UInt8) : MachineEvent → Prop
  | .absorb payload => payload.label ≠ forbiddenLabel
  | .challenge _ _ | .grind _ _ | .check _ => True

/-- Append the state-changing advance halves of a consumed duplex chain. -/
theorem pure_lookup_digest_chain_append_gamma
    {table : FixedOracleTable} {forbiddenLabel : UInt8}
    {boundaryInput : ShaInput} {initial digest : Digest256}
    (prefixChain : PureLookupDigestChain table boundaryInput
      (IsPurePostRootStateInput forbiddenLabel) initial digest)
    {outputs advances : List Digest256}
    (coordinates : GammaTableCoordinateChain table digest outputs advances) :
    PureLookupDigestChain table boundaryInput
      (IsPurePostRootStateInput forbiddenLabel) initial
        (gammaTerminalDigest digest advances) := by
  induction coordinates generalizing initial with
  | done => simpa [gammaTerminalDigest] using prefixChain
  | @next digest output advanced outputs advances outputLookup advanceLookup
      tail ih =>
      have causalPrefix :
          bytes digest = (gammaAdvanceInput digest).take 32 := by
        simp [gammaAdvanceInput, bytes_length]
      have allowed : IsPurePostRootStateInput forbiddenLabel
          (gammaAdvanceInput digest) := Or.inl ⟨digest, rfl⟩
      have advancedPrefix : PureLookupDigestChain table boundaryInput
          (IsPurePostRootStateInput forbiddenLabel) initial advanced :=
        .step initial digest advanced (gammaAdvanceInput digest) prefixChain
          causalPrefix allowed advanceLookup
      simpa [gammaTerminalDigest] using ih advancedPrefix

/-- Extend a pure lookup chain across one successful machine event. -/
theorem pure_lookup_digest_chain_through_machine_event
    (table : FixedOracleTable) {forbiddenLabel : UInt8}
    {boundaryInput : ShaInput} {initial : Digest256}
    (state next : EvalState) (event : MachineEvent)
    (chain : PureLookupDigestChain table boundaryInput
      (IsPurePostRootStateInput forbiddenLabel) initial state.digest)
    (allowedEvent : IsPurePostRootMachineEvent forbiddenLabel event)
    (run : runMachineEvent table state event = some next) :
    PureLookupDigestChain table boundaryInput
      (IsPurePostRootStateInput forbiddenLabel) initial next.digest := by
  cases event with
  | absorb payload =>
      let absorbInput :=
        bytes state.digest ++ [domAbsorb, payload.label] ++ payload.data
      have lookup : tableLookup table absorbInput = some next.digest := by
        simpa [absorbInput] using
          absorb_step_exposes_literal_lookup table state next payload run
      have causalPrefix : bytes state.digest = absorbInput.take 32 := by
        simp [absorbInput, bytes_length]
      have allowed : IsPurePostRootStateInput forbiddenLabel absorbInput := by
        unfold IsPurePostRootMachineEvent at allowedEvent
        exact Or.inr ⟨state.digest, payload, allowedEvent, rfl⟩
      exact .step initial state.digest next.digest absorbInput chain causalPrefix
        allowed lookup
  | challenge id use =>
      rw [runMachineEvent] at run
      obtain ⟨samplePair, squeezeRun, result⟩ :=
        Option.bind_eq_some_iff.mp run
      rcases samplePair with ⟨outputs, sampled⟩
      have nextExact :
          { sampled with
              samples := sampled.samples ++ [{ id := id, blocks := outputs }] } =
            next := by
        simpa only [pure, Option.some.injEq] using result
      subst next
      obtain ⟨advances, _advancesLength, coordinates, terminalExact,
          _callsExact⟩ :=
        squeeze_many_coordinates_with_terminal table (.challenge id)
          use.blocksUsed state sampled outputs squeezeRun
      have appended := pure_lookup_digest_chain_append_gamma chain coordinates
      simpa [terminalExact] using appended
  | grind stage choice =>
      have digestExact := grinding_choice_does_not_advance table state next
        stage choice run
      simpa [digestExact] using chain
  | check checkpoint =>
      have nextExact : next = state := by
        simpa [runMachineEvent] using (Option.some.inj run).symm
      subst next
      exact chain

/-- Iterate the event-local extraction over a successful event list. -/
theorem pure_lookup_digest_chain_through_machine_events
    (table : FixedOracleTable) {forbiddenLabel : UInt8}
    {boundaryInput : ShaInput} {initial : Digest256}
    (events : List MachineEvent) (state final : EvalState)
    (chain : PureLookupDigestChain table boundaryInput
      (IsPurePostRootStateInput forbiddenLabel) initial state.digest)
    (allowedEvents : ∀ event, event ∈ events →
      IsPurePostRootMachineEvent forbiddenLabel event)
    (run : runMachineEvents table events state = some final) :
    PureLookupDigestChain table boundaryInput
      (IsPurePostRootStateInput forbiddenLabel) initial final.digest := by
  induction events generalizing state with
  | nil =>
      have finalExact : final = state := by
        simpa [runMachineEvents] using (Option.some.inj run).symm
      subst final
      exact chain
  | cons event rest ih =>
      rw [runMachineEvents] at run
      obtain ⟨next, eventRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      have eventAllowed : IsPurePostRootMachineEvent forbiddenLabel event :=
        allowedEvents event (by simp)
      have nextChain := pure_lookup_digest_chain_through_machine_event table
        state next event chain eventAllowed eventRun
      apply ih next nextChain
      · intro later laterMember
        exact allowedEvents later (by simp [laterMember])
      · exact restRun

#print axioms PureLookupDigestChain
#print axioms pure_lookup_digest_chain_append_gamma
#print axioms pure_lookup_digest_chain_through_machine_event
#print axioms pure_lookup_digest_chain_through_machine_events

end AspisK1.V7Tag73PureLookupDigestChain
