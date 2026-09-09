import AspisFormal.K1.V7Tag73ExactDagQ16ChainRouting

/-!
# Terminal producer installation for an ordered q16 prefix

An installed block-zero producer and an exact root-ordered duplex chain imply
that the producer at the chain's terminal state is installed at the expected
counter/block slot.  This is the deterministic induction needed to connect
the selected q16 terminal source coordinate to the candidate-directed
query-batch observer.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactDagQ16TerminalProducer

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Recursively following the advance edges installs the producer at the
terminal state of the consumed prefix.  The returned source input is kept
existential because the zero-length case starts at the caller-supplied source,
while every successor case starts at a literal advance input. -/
theorem exact_ordered_q16_chain_installs_terminal_producer
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters)
    (counter : Fin 64) :
    ∀ {producerInput : ShaInput} {digest : Digest256}
      {outputs advances : List Digest256}
      (block : Fin 8)
      (chain : ExactRootOrderedQ16Chain input producerInput digest outputs
        advances)
      (terminalBound : block.val + outputs.length < 8)
      (installed : ExactDagProducerInstalled input trial
        (Q16DagProducer.mk digest (counter, block) producerInput)),
      ∃ terminalInput,
        ExactDagProducerInstalled input trial
          (Q16DagProducer.mk (gammaTerminalDigest digest advances)
            (counter,
              ⟨block.val + outputs.length, terminalBound⟩)
            terminalInput) := by
  intro producerInput digest outputs advances block chain terminalBound
    installed
  induction chain generalizing block with
  | done producerInput digest producerFound =>
      refine ⟨producerInput, ?_⟩
      simpa [gammaTerminalDigest] using installed
  | @next producerInput digest output advanced outputs advances producerFound
      outputFound advanceFound producerBeforeOutput producerBeforeAdvance tail
      ih =>
      have nextBound : block.val + 1 < 8 := by
        simp only [List.length_cons] at terminalBound
        omega
      let nextBlock : Fin 8 := ⟨block.val + 1, nextBound⟩
      let parent := Q16DagProducer.mk digest (counter, block) producerInput
      let nextProducer := Q16DagProducer.mk advanced (counter, nextBlock)
        (gammaAdvanceInput digest)
      have nextInstalled : ExactDagProducerInstalled input trial
          nextProducer := by
        have raw := exact_dag_advance_installs_next_producer input trial parent
          advanced nextBound installed (by
            simpa [parent, gammaAdvanceInput] using producerBeforeAdvance)
        simpa [parent, nextProducer, nextBlock] using raw
      have tailBound : nextBlock.val + outputs.length < 8 := by
        simp only [List.length_cons] at terminalBound
        simp [nextBlock]
        omega
      obtain ⟨terminalInput, terminalInstalled⟩ :=
        ih nextBlock tailBound nextInstalled
      refine ⟨terminalInput, ?_⟩
      simpa [nextBlock, gammaTerminalDigest, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using terminalInstalled

/-- A nonempty chain exposes its exact last parent producer together with the
fact that this very source input/digest pair is installed at the expected
slot.  This version preserves source identity without assuming SHA
injectivity. -/
theorem exact_ordered_q16_chain_last_parent_is_installed
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters)
    (counter : Fin 64) :
    ∀ {producerInput : ShaInput} {digest : Digest256}
      {outputs advances : List Digest256}
      (block : Fin 8)
      (chain : ExactRootOrderedQ16Chain input producerInput digest outputs
        advances)
      (nonempty : 0 < outputs.length)
      (lengthCap : block.val + outputs.length ≤ 8)
      (installed : ExactDagProducerInstalled input trial
        (Q16DagProducer.mk digest (counter, block) producerInput)),
      ∃ (prefixOutputs prefixAdvances : List Digest256)
          (blockProducerInput : ShaInput)
          (blockDigest blockOutput blockAdvance : Digest256)
          (lastBound : block.val + prefixOutputs.length < 8),
        outputs = prefixOutputs ++ [blockOutput] ∧
        advances = prefixAdvances ++ [blockAdvance] ∧
        ExactRootOrderedQ16Chain input producerInput digest prefixOutputs
          prefixAdvances ∧
        tableLookup (exactOperationalTable input) blockProducerInput =
          some blockDigest ∧
        tableLookup (exactOperationalTable input)
          (gammaOutputInput blockDigest) = some blockOutput ∧
        tableLookup (exactOperationalTable input)
          (gammaAdvanceInput blockDigest) = some blockAdvance ∧
        (∃ before middle after,
          exactRootFreshQueries input =
            before ++ (blockProducerInput, blockDigest) :: middle ++
              (gammaAdvanceInput blockDigest, blockAdvance) :: after) ∧
        gammaTerminalDigest digest prefixAdvances = blockDigest ∧
        gammaTerminalDigest digest advances = blockAdvance ∧
        ExactDagProducerInstalled input trial
          (Q16DagProducer.mk blockDigest
            (counter, ⟨block.val + prefixOutputs.length, lastBound⟩)
            blockProducerInput) := by
  intro producerInput digest outputs advances block chain nonempty lengthCap
    installed
  induction chain generalizing block with
  | done => simp at nonempty
  | @next producerInput digest output advanced outputs advances producerFound
      outputFound advanceFound producerBeforeOutput producerBeforeAdvance tail
      ih =>
      by_cases outputsEmpty : outputs = []
      · subst outputs
        have advancesEmpty : advances = [] := by
          apply List.length_eq_zero_iff.mp
          simpa using exact_root_ordered_q16_chain_lengths tail
        subst advances
        have lastBound :
            block.val + (List.nil : List Digest256).length < 8 := by
          simp only [List.length_cons] at lengthCap
          simp
        refine ⟨[], [], producerInput, digest, output, advanced, lastBound,
          rfl, rfl, .done producerInput digest producerFound, producerFound,
          outputFound, advanceFound, producerBeforeAdvance, rfl, rfl, ?_⟩
        simpa using installed
      · have tailNonempty : 0 < outputs.length := by
          exact Nat.pos_of_ne_zero (fun lengthZero =>
            outputsEmpty (List.length_eq_zero_iff.mp lengthZero))
        have nextBound : block.val + 1 < 8 := by
          simp only [List.length_cons] at lengthCap
          omega
        let nextBlock : Fin 8 := ⟨block.val + 1, nextBound⟩
        let parent := Q16DagProducer.mk digest (counter, block) producerInput
        let nextProducer := Q16DagProducer.mk advanced (counter, nextBlock)
          (gammaAdvanceInput digest)
        have nextInstalled : ExactDagProducerInstalled input trial
            nextProducer := by
          have raw := exact_dag_advance_installs_next_producer input trial
            parent advanced nextBound installed (by
              simpa [parent, gammaAdvanceInput] using producerBeforeAdvance)
          simpa [parent, nextProducer, nextBlock] using raw
        have tailCap : nextBlock.val + outputs.length ≤ 8 := by
          simp only [List.length_cons] at lengthCap
          simp [nextBlock]
          omega
        obtain ⟨prefixOutputs, prefixAdvances, blockProducerInput,
            blockDigest, blockOutput, blockAdvance, tailLastBound,
            outputsExact, advancesExact, prefixChain, blockProducerLookup,
            blockOutputLookup, blockAdvanceLookup, blockOrder,
            predecessorExact, terminalExact, terminalInstalled⟩ :=
          ih nextBlock tailNonempty tailCap nextInstalled
        have lastBound : block.val + (output :: prefixOutputs).length < 8 := by
          simp only [List.length_cons]
          simp [nextBlock] at tailLastBound
          omega
        refine ⟨output :: prefixOutputs, advanced :: prefixAdvances,
          blockProducerInput, blockDigest, blockOutput, blockAdvance, lastBound,
          ?_, ?_, ?_, blockProducerLookup, blockOutputLookup,
          blockAdvanceLookup, blockOrder, ?_, ?_, ?_⟩
        · simp only [List.cons_append]
          rw [outputsExact]
        · simp only [List.cons_append]
          rw [advancesExact]
        · exact .next producerFound outputFound advanceFound
            producerBeforeOutput producerBeforeAdvance prefixChain
        · simpa [gammaTerminalDigest] using predecessorExact
        · rw [advancesExact]
          exact gamma_terminal_digest_append_singleton digest blockAdvance
            (advanced :: prefixAdvances)
        · convert terminalInstalled using 1
          congr 1
          apply Prod.ext
          · rfl
          · apply Fin.ext
            simp [nextBlock]
            omega

#print axioms exact_ordered_q16_chain_installs_terminal_producer
#print axioms exact_ordered_q16_chain_last_parent_is_installed

end
end AspisK1.V7Tag73ExactDagQ16TerminalProducer
