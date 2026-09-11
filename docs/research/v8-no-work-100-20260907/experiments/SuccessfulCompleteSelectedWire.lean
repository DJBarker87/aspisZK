import SelectedWireMerkleRun
import SelectedAuthenticatedSuccessfulRun

/-! Headline composition: a successful selected Wire parse, Rust-shaped q22
opening verification, canonical packed-record parsing, checked inverse/local
terminal, and the nonterminal path checks construct the already-proved
`SuccessfulAt` execution and its ideal execution, or the explicit shared
hash/authentication failure union.

The functional Merkle verifier mirrors `v7_merkle208.rs`; equivalence to the
compiled mutable-Vec Rust execution remains the final lower refinement layer.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 250
set_option maxHeartbeats 300000

namespace AspisV8.SuccessfulCompleteSelectedWire
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisV8.AuthenticatedEarlyC1Prefix AspisV8.SuccessfulSelectedVerifierRun
open AspisV8.SelectedWireBytes AspisV8.SelectedWireMerkleRun
open AspisV8.RustShapedMinimalMultiproof AspisV8.MinimalMultiproofPaths
open AspisV8.SelectedMultiproofOpeningEquality
open AspisV8.SelectedAuthenticatedSuccessfulRun
open AspisV8.FixedWordQueryTerminal
noncomputable section

abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev M31 := AspisV5ComponentCQM31TowerExact.M31Exact
abbrev Byte := AspisPool.V7MerkleQueryGrammar.Byte
abbrev Digest208 := AspisPool.V7MerkleQueryGrammar.Digest208

/-- The Merkle acceptance, records, roots and frontiers are constructed from
the successful parsed Wire run.  `p` remains an independent field-level
program input: this theorem does **not** establish that its claims, OOD data,
responses, final256, weights or semantic context are constructed from `body`.
`OneWireConsumedFields` is the separate audit-repair leaf for literal
fixed-field projections; a full same-body source refinement must compose that
leaf with the public semantic/context and causal-prefix constructors. -/
theorem successful_complete_selected_wire_constructs_ideal_execution_or_auth_failure
    (p : Program 22) (c2Prefix : AnswerPrefix) (c2Root : Digest208)
    (view : RawHashInput → Digest208) (fullLog : OrderedRawQueryLog)
    (body : List Byte) (gamma kappa tau alpha : K)
    (queries : OrderedQueryGame.Schedule AspisV8.SelectedReceivedOracle.domain 22)
    (rho a1 a2 a3 : K)
    (merkle : SuccessfulMerkleRun view (indices queries) body)
    (rootBound : wireRoots merkle.wire = roots p c2Root)
    (decoded : Fin 22 → AspisV8.PackedQueryRecord.Decoded)
    (parsed : ∀ i, AspisV8.PackedQueryRecord.parse (merkle.wire.record i) = some (decoded i))
    (c1Answers : ∀ record ∈ p.earlyRecords, view record.1 = record.2)
    (c2Answers : ∀ record ∈ c2Prefix, view record.1 = record.2)
    (c1Included : TraceIncludedInLog (rawPrefix p.earlyRecords) fullLog)
    (c2Included : TraceIncludedInLog (rawPrefix c2Prefix) fullLog)
    (callsIncluded : TraceIncludedInLog
      (leafLog (indices queries) (wireRecords merkle.wire) ++ merkle.trace) fullLog)
    (checks : PathChecks (phaseProgram p c2Prefix c2Root)
      gamma kappa tau alpha queries rho a1 a2)
    (out : List K × List M31)
    (inverse : AspisV8.LineNormBuffer.inverseLines
      (fixedInput (phaseProgram p c2Prefix c2Root) gamma kappa).chord.a
      (fixedInput (phaseProgram p c2Prefix c2Root) gamma kappa).chord.b
      (fixedInput (phaseProgram p c2Prefix c2Root) gamma kappa).chord.c
      (AspisV8.SelectedQueryBuffer.points (indices queries)) = some out)
    (terminal : acceptsValues
      ((fixedInput (phaseProgram p c2Prefix c2Root) gamma kappa).before.snapshot
        tau ((fields (phaseProgram p c2Prefix c2Root) gamma kappa).firstResponse tau) alpha)
      ((fields (phaseProgram p c2Prefix c2Root) gamma kappa).final tau alpha)
      (fun j => (queries j : K))
      (openedValues (fixedInput (phaseProgram p c2Prefix c2Root) gamma kappa)
        decoded queries out alpha) rho
      ((fields (phaseProgram p c2Prefix c2Root) gamma kappa).later tau alpha queries rho)
      a1 a2 a3) :
    AuthenticationFailure view p.earlyRecords c2Prefix (roots p c2Root)
        fullLog (indices queries) ∨
      (SuccessfulAt (phaseProgram p c2Prefix c2Root)
        gamma kappa tau alpha queries rho a1 a2 a3 ∧
       AspisV8.SelectedAcceptedPrefixPartition.idealAccepts
        (phaseProgram p c2Prefix c2Root).execution
        gamma kappa tau alpha queries rho [a1,a2,a3]) := by
  have accepted := successful_constructs_accepted view (indices queries) body merkle
  rw [rootBound] at accepted
  exact wire_success_or_authentication_failure p c2Prefix c2Root view fullLog
    gamma kappa tau alpha queries rho a1 a2 a3
    (fun i => merkle.wire.record i) decoded
    (RustShapedMinimalMultiproof.frontierPairs
      (merkle.wire.frontiers 0) (merkle.wire.frontiers 1)) merkle.trace
    c1Answers c2Answers c1Included c2Included callsIncluded parsed accepted checks
    out inverse terminal

#print axioms successful_complete_selected_wire_constructs_ideal_execution_or_auth_failure
end
end AspisV8.SuccessfulCompleteSelectedWire
