import FSV7LeavesScript
import FSV7NodeVerifierScript
import SelectedWireMerkleRun

/-! Single-body chronological Merkle suffix. Parsed roots are compared with
the actual commitment-cut roots before leaf hashing. Records/frontiers come
only from the same parsed Wire. No independent program, pure verifier success,
opening trace or hash-view agreement is a constructor input.

This is a deterministic functional source constructor. Coupling this suffix
to the actual Rust caller and to the query sampler remains separate; its
query argument must be the caller's realised schedule. The preceding shared
state/root-cut chronology is provided by continueRun, not asserted here. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSV7SelectedBodyScript
open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSV7PrefixBridge
open FSV7LeavesScript FSV7NodeVerifierScript
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleOpeningBinding
open AspisPool.V7MerkleQueryExtractor
open AspisV8.MinimalMultiproofPaths AspisV8.RustShapedMinimalMultiproof
open AspisV8.SelectedWireBytes AspisV8.SelectedWireMerkleRun

def bodyAllowance (positions : Fin 22 → Position) : Nat :=
  2*22*18 + 2*(sortedOrdinals positions).length

def wireScript (cuts : RootCuts) (positions : Fin 22 → Position) (wire : Wire) :
    Script (List UInt8) Block OrderedRawQueryLog (bodyAllowance positions) :=
  if wire.roots 0 = root208 cuts.c1 ∧ wire.roots 1 = root208 cuts.c2 then
    bind (leavesScript positions (wireRecords wire) (sortedOrdinals positions)) fun entries =>
      nodeVerifierScript (wireRoots wire) entries (wire.frontiers 0) (wire.frontiers 1)
  else .abort

def selectedScript (cuts : RootCuts) (positions : Fin 22 → Position)
    (body : List AspisPool.V7MerkleQueryGrammar.Byte) :
    Script (List UInt8) Block OrderedRawQueryLog (bodyAllowance positions) :=
  match AspisV8.SelectedWireBytes.parse body with
  | none => .abort
  | some wire => wireScript cuts positions wire

theorem wire_constructs (tape : Tape) (cuts : RootCuts) (positions : Fin 22 → Position)
    (wire : Wire) (s : Oracle) (trace : OrderedRawQueryLog)
    (coherent : FSExposureOrder.LogConsistent s)
    (success : (run tape (wireScript cuts positions wire) s).1 = some trace) :
    wire.roots 0 = root208 cuts.c1 ∧ wire.roots 1 = root208 cuts.c2 ∧
    verify (oldView (run tape (wireScript cuts positions wire) s).2) (wireRoots wire) 18
      (sortedEntries (oldView (run tape (wireScript cuts positions wire) s).2)
        positions (wireRecords wire)) (wire.frontiers 0) (wire.frontiers 1) = some trace ∧
    oldLog (run tape (wireScript cuts positions wire) s).2 =
      oldLog s ++ (leafLog positions (wireRecords wire) ++ trace) := by
  unfold wireScript bodyAllowance at success ⊢
  by_cases roots : wire.roots 0 = root208 cuts.c1 ∧ wire.roots 1 = root208 cuts.c2
  · simp only [if_pos roots, run_bind] at success ⊢
    cases leavesRun : (run tape
        (leavesScript positions (wireRecords wire) (sortedOrdinals positions)) s).1 with
    | none => simp only [leavesRun, reduceCtorEq] at success
    | some entries =>
      simp only [leavesRun] at success ⊢
      have afterLeaves := FSExposureOrder.run_log_consistent tape
        (leavesScript positions (wireRecords wire) (sortedOrdinals positions)) s coherent
      obtain ⟨verified, nodeLog⟩ := node_verifier_constructs tape (wireRoots wire) entries
        (wire.frontiers 0) (wire.frontiers 1) _ trace afterLeaves success
      obtain ⟨leafValues, _⟩ := leaves_through_later tape positions (wireRecords wire)
        (sortedOrdinals positions) s entries
        (nodeVerifierScript (wireRoots wire) entries (wire.frontiers 0) (wire.frontiers 1))
        coherent leavesRun
      obtain ⟨_, leafLogExact⟩ := leaves_refines tape positions (wireRecords wire)
        (sortedOrdinals positions) s entries leavesRun
      refine ⟨roots.1, roots.2, ?_, ?_⟩
      · change entries = sortedEntries
          (oldView (run tape (nodeVerifierScript (wireRoots wire) entries
            (wire.frontiers 0) (wire.frontiers 1))
            (run tape (leavesScript positions (wireRecords wire) (sortedOrdinals positions)) s).2).2)
          positions (wireRecords wire) at leafValues
        simpa only [← leafValues] using verified
      · rw [nodeLog, leafLogExact]
        exact List.append_assoc _ _ _
  · simp only [if_neg roots, run, reduceCtorEq] at success

/-- Successful same-body execution constructs the exact old wire verifier
object and its complete actual leaf+node call inclusion. Neither is supplied.
The source schedule and reachable starting coherence remain explicit inputs. -/
theorem selected_constructs (tape : Tape) (cuts : RootCuts) (positions : Fin 22 → Position)
    (body : List AspisPool.V7MerkleQueryGrammar.Byte) (s : Oracle) (trace : OrderedRawQueryLog)
    (coherent : FSExposureOrder.LogConsistent s)
    (success : (run tape (selectedScript cuts positions body) s).1 = some trace) :
    ∃ merkle : SuccessfulMerkleRun (oldView (run tape (selectedScript cuts positions body) s).2)
        positions body,
      merkle.trace = trace ∧ merkle.wire.roots 0 = root208 cuts.c1 ∧
      merkle.wire.roots 1 = root208 cuts.c2 ∧
      TraceIncludedInLog (leafLog positions (wireRecords merkle.wire) ++ merkle.trace)
        (oldLog (run tape (selectedScript cuts positions body) s).2) := by
  unfold selectedScript at success ⊢
  cases parsed : AspisV8.SelectedWireBytes.parse body with
  | none => simp only [parsed, run, reduceCtorEq] at success
  | some wire =>
    simp only [parsed] at success ⊢
    obtain ⟨root0, root1, verified, exactLog⟩ :=
      wire_constructs tape cuts positions wire s trace coherent success
    refine ⟨⟨wire, parsed, trace, verified⟩, rfl, root0, root1, ?_⟩
    intro input member
    rw [exactLog]
    exact List.mem_append.mpr (Or.inr member)

#print selected_constructs
#print axioms wire_constructs
#print axioms selected_constructs
end AspisV8Completion.FSV7SelectedBodyScript
