import FSTranscriptScript
set_option autoImplicit false
namespace AspisV8Completion.FSAuthenticationPrefixes
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
abbrev Bytes := List UInt8
abbrev AnswerRecord := Bytes × Bytes

/-- The literal source `digest[..26]`; the shared oracle still stores all32.
Distinct full answers or distinct inputs may project to the same digest. -/
def truncate208 (answer : Block) : Bytes := (List.ofFn answer).take 26
def records (log : List (Event Bytes Block)) : List AnswerRecord :=
  log.map (fun event => (event.input, truncate208 event.answer))
def view208 (oracle : Oracle) (input : Bytes) : Option Bytes :=
  (oracle.cache input).map truncate208
def totalView208 (oracle : Oracle) (input : Bytes) : Bytes :=
  (view208 oracle input).getD (List.replicate 26 0)

theorem truncate_length (answer : Block) : (truncate208 answer).length = 26 := by
  simp [truncate208]

theorem records_length (log : List (Event Bytes Block)) :
    (records log).length = log.length := by simp [records]

theorem records_take (log : List (Event Bytes Block)) (cut : Nat) :
    records (log.take cut) = (records log).take cut := by simp [records, List.map_take]

theorem record_answer (oracle : Oracle) (valid : FSFirstFresh.ValidHistory oracle)
    (record : AnswerRecord) (member : record ∈ records oracle.log) :
    view208 oracle record.1 = some record.2 := by
  obtain ⟨event, seen, eq⟩ := List.mem_map.mp member
  subst record
  simp only [view208, valid.coherent event seen, Option.map_some]

theorem early_result_final {n : Nat} (tape : Tape) (initial : Transcript) (root1 : Root)
    (producer : Oracle → List Nat → List Nat → Script Bytes Block Root n) (out : RootCuts)
    (success : (earlyWithC2 tape initial root1 producer).1 = some out) :
    (earlyWithC2 tape initial root1 producer).2 = out.final := by
  simp only [earlyWithC2] at success ⊢
  split at success
  · contradiction
  · split at success
    · contradiction
    · split at success
      · contradiction
      · cases success; simp_all only

theorem result_final {n m : Nat} (tape : Tape) (initial : Transcript)
    (producerC1 : Transcript → Script Bytes Block Root n)
    (producerC2 : Oracle → List Nat → List Nat → Script Bytes Block Root m)
    (out : RootCuts) (success : (constructBoth tape initial producerC1 producerC2).1 = some out) :
    (constructBoth tape initial producerC1 producerC2).2 = out.final := by
  simp only [constructBoth] at success ⊢
  split at success
  · contradiction
  · exact early_result_final tape _ _ producerC2 out success

/-- Source-produced prefixes, not separately supplied answer logs. Both cuts
are after their actual builder calls and before the corresponding root absorb. -/
def c1Records (out : RootCuts) := records out.c1Cut.log
def c2Records (out : RootCuts) := records out.c2Cut.log

theorem projected_cuts {n m : Nat} (tape : Tape) (initial : Transcript)
    (producerC1 : Transcript → Script Bytes Block Root n)
    (producerC2 : Oracle → List Nat → List Nat → Script Bytes Block Root m)
    (out : RootCuts) (success : (constructBoth tape initial producerC1 producerC2).1 = some out) :
    out.c1Cut.log.length ≤ out.c2Cut.log.length ∧
    out.c2Cut.log.length ≤ out.final.oracle.log.length ∧
    c1Records out = (records out.final.oracle.log).take out.c1Cut.log.length ∧
    c2Records out = (records out.final.oracle.log).take out.c2Cut.log.length := by
  obtain ⟨_, between, afterCut⟩ := constructed_cuts tape initial producerC1 producerC2 out success
  obtain ⟨a, ha⟩ := between
  obtain ⟨b, hb⟩ := afterCut
  constructor
  · simp [ha]
  constructor
  · simp [hb]
  constructor
  · simp [c1Records, hb, ha, records, List.map_append, List.append_assoc]
  · simp [c2Records, hb, records, List.map_append]

/-- Complete deterministic endpoint from one actual empty-start execution:
the two root-bound answer prefixes are chronological takes of its final log,
and every advertised answer agrees with that SAME final full-answer cache.
No cache→log, log→cache, subset, root-equality-only, or collision-free premise
is supplied by the caller. Root bytes themselves are produced by the scripts. -/
theorem projected_answers_from_empty {n m : Nat} (tape : Tape) (digest : Block)
    (producerC1 : Transcript → Script Bytes Block Root n)
    (producerC2 : Oracle → List Nat → List Nat → Script Bytes Block Root m)
    (out : RootCuts)
    (success : (constructBoth tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2).1 = some out) :
    (∀ record ∈ c1Records out, view208 out.final.oracle record.1 = some record.2) ∧
    (∀ record ∈ c2Records out, view208 out.final.oracle record.1 = some record.2) ∧
    c1Records out = (records out.final.oracle.log).take out.c1Cut.log.length ∧
    c2Records out = (records out.final.oracle.log).take out.c2Cut.log.length := by
  have valid := constructBoth_valid_from_empty tape digest producerC1 producerC2
  rw [result_final tape _ producerC1 producerC2 out success] at valid
  obtain ⟨_, _, one, two⟩ := projected_cuts tape _ producerC1 producerC2 out success
  refine ⟨?_, ?_, one, two⟩
  · intro record member
    rw [one] at member
    exact record_answer out.final.oracle valid record (List.mem_of_mem_take member)
  · intro record member
    rw [two] at member
    exact record_answer out.final.oracle valid record (List.mem_of_mem_take member)

/-- Supplies the concrete advertised-answer premise of a prefix-authentication
consumer. The old consumer's RawHashInput/Digest208 type conversion and full
input grammar are NOT silently identified with these byte-list types. -/
theorem advertised_total_answers_from_empty {n m : Nat} (tape : Tape) (digest : Block)
    (producerC1 : Transcript → Script Bytes Block Root n)
    (producerC2 : Oracle → List Nat → List Nat → Script Bytes Block Root m)
    (out : RootCuts)
    (success : (constructBoth tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2).1 = some out) :
    (∀ record ∈ c1Records out, totalView208 out.final.oracle record.1 = record.2) ∧
    (∀ record ∈ c2Records out, totalView208 out.final.oracle record.1 = record.2) := by
  obtain ⟨one, two, _, _⟩ := projected_answers_from_empty tape digest producerC1 producerC2 out success
  constructor
  · intro record member; simp only [totalView208, one record member, Option.getD_some]
  · intro record member; simp only [totalView208, two record member, Option.getD_some]

private def zero : Block := fun _ => 0
private def samePrefix : Block := fun i => if i.val < 26 then 0 else 1
/- Projection deliberately permits collisions; no full-answer or input
injectivity is hidden in the invariant. The underlying full log is unchanged. -/
#guard truncate208 zero == truncate208 samePrefix
private def fixture := constructBoth (fun _ => zero) ⟨zero, FSFirstFresh.empty⟩
  (fun _ => Script.ask [98] (fun _ => Script.done (fun _ => 0) (n := 0)))
  (fun _ _ _ => Script.ask [99] (fun _ => Script.done (fun _ => 0) (n := 0)))
#guard fixture.1.isSome
#guard (fixture.1.map (fun out => (c1Records out).length)) == some 1
#guard (fixture.1.map (fun out => (c2Records out).length)) == some 7
#guard (records fixture.2.oracle.log).length == 8

#print axioms projected_cuts
#print axioms projected_answers_from_empty
#print axioms truncate_length
#print axioms advertised_total_answers_from_empty
end AspisV8Completion.FSAuthenticationPrefixes
