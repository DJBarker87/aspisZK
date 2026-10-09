import FSV7ViewPersistence

/-! Exact record leaf asks, C1 then C2, with arbitrary subsequent legal script.
The list producer consumes actual record ordinals in its supplied order; the
selected wrapper uses sortedOrdinals. Cached identical inputs remain actual
recorded calls, and all full256 answers stay in the shared oracle state. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSV7LeavesScript
open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSV7PrefixBridge
open FSV7ParentScript FSV7ViewPersistence
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleOpeningBinding
open AspisPool.V7MerkleQueryExtractor
open AspisV8.MinimalMultiproofPaths

def leafCompute (tape : Tape) (s : Oracle) (position : Nat) (record : Record) : Entry × Oracle :=
  let first := query tape s (decode (leafInput record 0))
  let second := query tape first.2 (decode (leafInput record 1))
  (⟨position, paired (answer208 first.1) (answer208 second.1)⟩, second.2)

def leafScript (position : Nat) (record : Record) : Script (List UInt8) Block Entry 2 :=
  .ask (decode (leafInput record 0)) fun first =>
    .ask (decode (leafInput record 1)) fun second =>
      .done ⟨position, paired (answer208 first) (answer208 second)⟩

theorem run_leaf (tape : Tape) (s : Oracle) (position : Nat) (record : Record) :
    run tape (leafScript position record) s =
      (some (leafCompute tape s position record).1, (leafCompute tape s position record).2) := rfl

theorem leaf_log (tape : Tape) (s : Oracle) (position : Nat) (record : Record) :
    oldLog (leafCompute tape s position record).2 = oldLog s ++ leafCalls record := by
  simp only [leafCompute, query_oldLog, leafCalls, List.append_assoc]
  rfl

theorem leaf_value_after_script {A : Type} {q : Nat} (tape : Tape) (s : Oracle)
    (position : Nat) (record : Record) (later : Script (List UInt8) Block A q) :
    (leafCompute tape s position record).1 =
      ⟨position, fun side => oldView (run tape later (leafCompute tape s position record).2).2
        (leafInput record side)⟩ := by
  let first := query tape s (decode (leafInput record 0))
  let second := query tape first.2 (decode (leafInput record 1))
  have firstStored : first.2.cache (decode (leafInput record 0)) = some first.1 :=
    answer_installed tape s _
  have secondStored : second.2.cache (decode (leafInput record 1)) = some second.1 :=
    answer_installed tape first.2 _
  have firstStill : second.2.cache (decode (leafInput record 0)) = some first.1 :=
    old_answer_preserved tape first.2 _ _ first.1 firstStored
  have final0 := run_preserves_answer tape later second.2 _ first.1 firstStill
  have final1 := run_preserves_answer tape later second.2 _ second.1 secondStored
  have value0 : oldView (run tape later second.2).2 (leafInput record 0) = answer208 first.1 := by
    simp only [oldView, FSAuthenticationPrefixes.totalView208, FSAuthenticationPrefixes.view208,
      final0, Option.map_some, Option.getD_some, answer208]
  have value1 : oldView (run tape later second.2).2 (leafInput record 1) = answer208 second.1 := by
    simp only [oldView, FSAuthenticationPrefixes.totalView208, FSAuthenticationPrefixes.view208,
      final1, Option.map_some, Option.getD_some, answer208]
  change (⟨position, paired (answer208 first.1) (answer208 second.1)⟩ : Entry) =
    ⟨position, fun side => oldView (run tape later second.2).2 (leafInput record side)⟩
  congr 1
  funext side
  fin_cases side
  · exact value0.symm
  · exact value1.symm

def leavesScript (positions : Fin 22 → Position) (records : Fin 22 → Record) :
    (indices : List (Fin 22)) → Script (List UInt8) Block (List Entry) (2*indices.length)
  | [] => .done []
  | i :: rest =>
    bind (leafScript (positions i).val (records i)) fun entry =>
      map (List.cons entry) (leavesScript positions records rest)

theorem leaves_refines (tape : Tape) (positions : Fin 22 → Position) (records : Fin 22 → Record)
    (indices : List (Fin 22)) (s : Oracle) (entries : List Entry)
    (success : (run tape (leavesScript positions records indices) s).1 = some entries) :
    entries = indices.map (recordEntry (oldView (run tape (leavesScript positions records indices) s).2)
      positions records) ∧
    oldLog (run tape (leavesScript positions records indices) s).2 =
      oldLog s ++ indices.flatMap (fun i => leafCalls (records i)) := by
  induction indices generalizing s entries with
  | nil =>
    simp only [leavesScript, run, Option.some.injEq] at success
    subst entries
    exact ⟨rfl, (List.append_nil _).symm⟩
  | cons i rest ih =>
    simp only [leavesScript, run_bind, run_leaf, run_map] at success ⊢
    cases tailRun : (run tape (leavesScript positions records rest)
        (leafCompute tape s (positions i).val (records i)).2).1 with
    | none => simp only [tailRun, Option.map_none, reduceCtorEq] at success
    | some tailEntries =>
      simp only [tailRun, Option.map_some, Option.some.injEq] at success
      subst entries
      obtain ⟨tailValues, tailLog⟩ := ih (leafCompute tape s (positions i).val (records i)).2
        tailEntries tailRun
      constructor
      · rw [List.map_cons, tailValues]
        congr 1
        exact leaf_value_after_script tape s (positions i).val (records i)
          (leavesScript positions records rest)
      · rw [tailLog, leaf_log]
        exact List.append_assoc _ _ _

theorem records_view_congr (left right : RawHashInput → Digest208)
    (positions : Fin 22 → Position) (records : Fin 22 → Record) (indices : List (Fin 22))
    (same : ∀ input ∈ indices.flatMap (fun i => leafCalls (records i)), left input = right input) :
    indices.map (recordEntry left positions records) =
      indices.map (recordEntry right positions records) := by
  apply List.map_congr_left
  intro i member
  unfold recordEntry
  congr 1
  funext side
  apply same
  apply List.mem_flatMap.mpr
  refine ⟨i, member, ?_⟩
  fin_cases side
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem leaves_through_later {A : Type} {q : Nat} (tape : Tape)
    (positions : Fin 22 → Position) (records : Fin 22 → Record) (indices : List (Fin 22))
    (s : Oracle) (entries : List Entry) (later : Script (List UInt8) Block A q)
    (coherent : FSExposureOrder.LogConsistent s)
    (success : (run tape (leavesScript positions records indices) s).1 = some entries) :
    entries = indices.map (recordEntry
      (oldView (run tape later (run tape (leavesScript positions records indices) s).2).2)
      positions records) ∧
    TraceIncludedInLog (indices.flatMap (fun i => leafCalls (records i)))
      (oldLog (run tape later (run tape (leavesScript positions records indices) s).2).2) := by
  obtain ⟨values, exactLog⟩ := leaves_refines tape positions records indices s entries success
  have afterLeaves := FSExposureOrder.run_log_consistent tape
    (leavesScript positions records indices) s coherent
  have included : TraceIncludedInLog (indices.flatMap (fun i => leafCalls (records i)))
      (oldLog (run tape (leavesScript positions records indices) s).2) := by
    intro input member
    rw [exactLog]
    exact List.mem_append.mpr (Or.inr member)
  constructor
  · rw [values]
    apply records_view_congr
    intro input member
    exact (logged_view_preserved tape _ later afterLeaves input (included input member)).symm
  · obtain ⟨suffix, suffixLog⟩ := run_extends tape later
      (run tape (leavesScript positions records indices) s).2
    intro input member
    simp only [oldLog, suffixLog, List.map_append]
    exact List.mem_append.mpr (Or.inl (included input member))

#print leaves_through_later
#print axioms leaf_value_after_script
#print axioms leaves_refines
#print axioms records_view_congr
#print axioms leaves_through_later
end AspisV8Completion.FSV7LeavesScript
