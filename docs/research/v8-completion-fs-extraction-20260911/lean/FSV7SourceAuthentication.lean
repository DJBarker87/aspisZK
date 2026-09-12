import FSV7SelectedBodyScript

/-! The chronological source join. Both commitments are built through legal
bounded scripts in the shared cached oracle; the selected same-body Merkle
suffix starts from the ACTUAL returned state. Thus initial coherence, root
identity, both prefix cuts, prefix answers and leaf/node call inclusion are
constructed rather than supplied as independent authentication interfaces.

This still is not literal Rust refinement or a sampler/ROM probability lift.
The schedule is an explicit realised source input, and this bounded slice
does not yet run the intervening semantic/OOD/relation transcript. Its accepted
outcome means this concrete Merkle slice succeeded, not payment acceptance.
Both early failure and later abort remain explicit in the interpreter. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSV7SourceAuthentication
open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSAuthenticationSuffix
open FSAuthenticationPrefixes FSV7PrefixBridge FSV7SelectedBodyScript
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisV8.MinimalMultiproofPaths AspisV8.SelectedWireMerkleRun
open AspisV8.AuthenticatedEarlyC1Prefix

def runSelected {n m : Nat} (tape : Tape) (digest : Block)
    (producerC1 : Transcript → Script (List UInt8) Block Root n)
    (producerC2 : Oracle → List Nat → List Nat → Script (List UInt8) Block Root m)
    (positions : Fin 22 → Position) (body : List AspisPool.V7MerkleQueryGrammar.Byte) :
    Option (RootCuts × Option OrderedRawQueryLog) × Oracle :=
  continueRun tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2
    (fun cuts => selectedScript cuts positions body)

theorem success_decomposes {n m : Nat} (tape : Tape) (digest : Block)
    (producerC1 : Transcript → Script (List UInt8) Block Root n)
    (producerC2 : Oracle → List Nat → List Nat → Script (List UInt8) Block Root m)
    (positions : Fin 22 → Position) (body : List AspisPool.V7MerkleQueryGrammar.Byte)
    (cuts : RootCuts) (trace : OrderedRawQueryLog)
    (success : (runSelected tape digest producerC1 producerC2 positions body).1 = some (cuts, some trace)) :
    (constructBoth tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2).1 = some cuts ∧
    (run tape (selectedScript cuts positions body)
      (constructBoth tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2).2.oracle).1 = some trace ∧
    (runSelected tape digest producerC1 producerC2 positions body).2 =
      (run tape (selectedScript cuts positions body)
        (constructBoth tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2).2.oracle).2 := by
  cases early : (constructBoth tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2).1 with
  | none => simp only [runSelected, continueRun, early] at success; contradiction
  | some produced =>
    have both := Option.some.inj (by simpa only [runSelected, continueRun, early] using success)
    have same : produced = cuts := congrArg Prod.fst both
    subst produced
    refine ⟨by simp only [early], congrArg Prod.snd both, ?_⟩
    simp only [runSelected, continueRun, early]

/-- The coherence premise of selected_constructs is discharged from the real
empty-origin builder execution. No view, Merkle run or prefix supplied. -/
theorem source_constructs_merkle {n m : Nat} (tape : Tape) (digest : Block)
    (producerC1 : Transcript → Script (List UInt8) Block Root n)
    (producerC2 : Oracle → List Nat → List Nat → Script (List UInt8) Block Root m)
    (positions : Fin 22 → Position) (body : List AspisPool.V7MerkleQueryGrammar.Byte)
    (cuts : RootCuts) (trace : OrderedRawQueryLog)
    (success : (runSelected tape digest producerC1 producerC2 positions body).1 = some (cuts, some trace)) :
    ∃ merkle : SuccessfulMerkleRun
        (oldView (runSelected tape digest producerC1 producerC2 positions body).2) positions body,
      merkle.trace = trace ∧ merkle.wire.roots 0 = root208 cuts.c1 ∧
      merkle.wire.roots 1 = root208 cuts.c2 ∧
      TraceIncludedInLog (leafLog positions (wireRecords merkle.wire) ++ merkle.trace)
        (oldLog (runSelected tape digest producerC1 producerC2 positions body).2) := by
  obtain ⟨_, suffixSuccess, finalExact⟩ :=
    success_decomposes tape digest producerC1 producerC2 positions body cuts trace success
  have coherent := (constructBoth_valid_from_empty tape digest producerC1 producerC2).coherent
  rw [finalExact]
  exact selected_constructs tape cuts positions body _ trace coherent suffixSuccess

/-- All chronological authentication interfaces are OUTPUTS of one concrete
execution. The initial cache is empty; earlier adversary prequeries may occur
inside the C1 builder and are retained before its actual commitment cut. -/
theorem source_authentication_inputs {n m : Nat} (tape : Tape) (digest : Block)
    (producerC1 : Transcript → Script (List UInt8) Block Root n)
    (producerC2 : Oracle → List Nat → List Nat → Script (List UInt8) Block Root m)
    (positions : Fin 22 → Position) (body : List AspisPool.V7MerkleQueryGrammar.Byte)
    (cuts : RootCuts) (trace : OrderedRawQueryLog)
    (success : (runSelected tape digest producerC1 producerC2 positions body).1 = some (cuts, some trace)) :
    let final := (runSelected tape digest producerC1 producerC2 positions body).2
    FSFirstFresh.ValidHistory final ∧
    Prefix cuts.c1Cut cuts.c2Cut ∧ Prefix cuts.c2Cut final ∧
    (∀ record ∈ oldRecords (c1Records cuts), oldView final record.1 = record.2) ∧
    (∀ record ∈ oldRecords (c2Records cuts), oldView final record.1 = record.2) ∧
    TraceIncludedInLog (rawPrefix (oldRecords (c1Records cuts))) (oldLog final) ∧
    TraceIncludedInLog (rawPrefix (oldRecords (c2Records cuts))) (oldLog final) ∧
    rawPrefix (oldRecords (c1Records cuts)) = (oldLog final).take cuts.c1Cut.log.length ∧
    rawPrefix (oldRecords (c2Records cuts)) = (oldLog final).take cuts.c2Cut.log.length ∧
    ∃ merkle : SuccessfulMerkleRun (oldView final) positions body,
      merkle.trace = trace ∧ merkle.wire.roots 0 = root208 cuts.c1 ∧
      merkle.wire.roots 1 = root208 cuts.c2 ∧
      TraceIncludedInLog (leafLog positions (wireRecords merkle.wire) ++ merkle.trace) (oldLog final) := by
  dsimp only
  obtain ⟨early, _, finalExact⟩ :=
    success_decomposes tape digest producerC1 producerC2 positions body cuts trace success
  have history := continue_valid tape digest producerC1 producerC2
    (fun cuts => selectedScript cuts positions body)
  obtain ⟨_, firstSecond, secondEarly⟩ :=
    constructed_cuts tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2 cuts early
  have stateExact := result_final tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2 cuts early
  have secondFinal : Prefix cuts.c2Cut (runSelected tape digest producerC1 producerC2 positions body).2 := by
    rw [finalExact, stateExact]
    exact prefix_trans secondEarly (run_extends tape (selectedScript cuts positions body) cuts.final.oracle)
  obtain ⟨answers1, answers2, included1, included2, take1, take2⟩ :=
    chronological_old_prefixes tape digest producerC1 producerC2
      (fun cuts => selectedScript cuts positions body) cuts (some trace) success
  exact ⟨history, firstSecond, secondFinal, answers1, answers2, included1, included2, take1, take2,
    source_constructs_merkle tape digest producerC1 producerC2 positions body cuts trace success⟩

#print source_authentication_inputs
#print axioms success_decomposes
#print axioms source_constructs_merkle
#print axioms source_authentication_inputs
end AspisV8Completion.FSV7SourceAuthentication
