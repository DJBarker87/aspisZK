import FSAuthenticationPrefixes
set_option autoImplicit false
namespace AspisV8Completion.FSAuthenticationSuffix
open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSAuthenticationPrefixes
variable {A : Type}

/-- Execute later legal source/adversary calls from the ACTUAL returned oracle.
The suffix selector sees only the completed early prefix. Outer none means
early failure. Inner none means the later script aborted, retaining every call;
outer some alone is emphatically not acceptance by the complete verifier. -/
def continueRun {n m q : Nat} (tape : Tape) (initial : Transcript)
    (producerC1 : Transcript → Script Bytes Block Root n)
    (producerC2 : Oracle → List Nat → List Nat → Script Bytes Block Root m)
    (suffix : RootCuts → Script Bytes Block A q) : Option (RootCuts × Option A) × Oracle :=
  let early := constructBoth tape initial producerC1 producerC2
  match early.1 with
  | none => (none, early.2.oracle)
  | some roots =>
      let later := run tape (suffix roots) early.2.oracle
      (some (roots, later.1), later.2)

/-- Neither early nor late abort discards the actual coherent history. -/
theorem continue_valid {n m q : Nat} (tape : Tape) (digest : Block)
    (producerC1 : Transcript → Script Bytes Block Root n)
    (producerC2 : Oracle → List Nat → List Nat → Script Bytes Block Root m)
    (suffix : RootCuts → Script Bytes Block A q) :
    FSFirstFresh.ValidHistory
      (continueRun tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2 suffix).2 := by
  have earlyValid := constructBoth_valid_from_empty tape digest producerC1 producerC2
  simp only [continueRun]
  split
  · exact earlyValid
  · exact FSFirstFresh.run_valid tape _ _ earlyValid

theorem later_call_bound {n m q : Nat} (tape : Tape) (initial : Transcript)
    (producerC1 : Transcript → Script Bytes Block Root n)
    (producerC2 : Oracle → List Nat → List Nat → Script Bytes Block Root m)
    (suffix : RootCuts → Script Bytes Block A q) :
    (continueRun tape initial producerC1 producerC2 suffix).2.log.length ≤
      (constructBoth tape initial producerC1 producerC2).2.oracle.log.length + q := by
  simp only [continueRun]
  split
  · exact Nat.le_add_right _ _
  · exact call_bound tape _ _

theorem extended_prefixes {n m q : Nat} (tape : Tape) (digest : Block)
    (producerC1 : Transcript → Script Bytes Block Root n)
    (producerC2 : Oracle → List Nat → List Nat → Script Bytes Block Root m)
    (suffix : RootCuts → Script Bytes Block A q) (out : RootCuts)
    (success : (constructBoth tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2).1 = some out) :
    let final := (run tape (suffix out) out.final.oracle).2
    FSFirstFresh.ValidHistory final ∧
    c1Records out = (records final.log).take out.c1Cut.log.length ∧
    c2Records out = (records final.log).take out.c2Cut.log.length ∧
    (∀ record ∈ c1Records out, totalView208 final record.1 = record.2) ∧
    (∀ record ∈ c2Records out, totalView208 final record.1 = record.2) := by
  have earlyValid := constructBoth_valid_from_empty tape digest producerC1 producerC2
  rw [result_final tape _ producerC1 producerC2 out success] at earlyValid
  have finalValid := FSFirstFresh.run_valid tape (suffix out) out.final.oracle earlyValid
  obtain ⟨_, twoBound, one, two⟩ := projected_cuts tape _ producerC1 producerC2 out success
  obtain ⟨tail, tailEq⟩ := run_extends tape (suffix out) out.final.oracle
  have oneBound : out.c1Cut.log.length ≤ out.final.oracle.log.length := by
    obtain ⟨h, _, _, _⟩ := projected_cuts tape _ producerC1 producerC2 out success
    exact Nat.le_trans h twoBound
  have oneFinal : c1Records out =
      (records (run tape (suffix out) out.final.oracle).2.log).take out.c1Cut.log.length := by
    rw [tailEq]
    simp only [records, List.map_append]
    rw [List.take_append_of_le_length (by simpa only [List.length_map] using oneBound)]
    exact one
  have twoFinal : c2Records out =
      (records (run tape (suffix out) out.final.oracle).2.log).take out.c2Cut.log.length := by
    rw [tailEq]
    simp only [records, List.map_append]
    rw [List.take_append_of_le_length (by simpa only [List.length_map] using twoBound)]
    exact two
  refine ⟨finalValid, oneFinal, twoFinal, ?_, ?_⟩
  · intro record member
    rw [oneFinal] at member
    have answer := record_answer _ finalValid record (List.mem_of_mem_take member)
    simp only [totalView208, answer, Option.getD_some]
  · intro record member
    rw [twoFinal] at member
    have answer := record_answer _ finalValid record (List.mem_of_mem_take member)
    simp only [totalView208, answer, Option.getD_some]

/-- Constructor endpoint: both prefix records are literal takes of the
full LATER log produced by this run, and all their advertised answers agree
with its full-answer cache. Inclusion and coherence are conclusions.
Later failure is retained, not dropped by requiring outcome=some value. -/
theorem continued_prefix_answers {n m q : Nat} (tape : Tape) (digest : Block)
    (producerC1 : Transcript → Script Bytes Block Root n)
    (producerC2 : Oracle → List Nat → List Nat → Script Bytes Block Root m)
    (suffix : RootCuts → Script Bytes Block A q) (out : RootCuts) (outcome : Option A)
    (success : (continueRun tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2 suffix).1 =
      some (out, outcome)) :
    let final := (continueRun tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2 suffix).2
    FSFirstFresh.ValidHistory final ∧
    c1Records out = (records final.log).take out.c1Cut.log.length ∧
    c2Records out = (records final.log).take out.c2Cut.log.length ∧
    (∀ record ∈ c1Records out, totalView208 final record.1 = record.2) ∧
    (∀ record ∈ c2Records out, totalView208 final record.1 = record.2) := by
  cases h : (constructBoth tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2).1 with
  | none => simp only [continueRun, h] at success; contradiction
  | some roots =>
      have equality : roots = out := by
        have both := Option.some.inj (by simpa only [continueRun, h] using success)
        exact congrArg Prod.fst both
      subst roots
      have proven := extended_prefixes tape digest producerC1 producerC2 suffix out h
      simpa only [continueRun, h, result_final tape _ producerC1 producerC2 out h] using proven

/- Controls: suffix hash inputs may repeat earlier builder queries or introduce
new opening inputs. Every call remains logged even when the suffix aborts. -/
private def zero : Block := fun _ => 0
private def c1 (_ : Transcript) : Script Bytes Block Root 1 :=
  .ask [98] (fun _ => .done (fun _ => 0))
private def c2 (_ : Oracle) (_ _ : List Nat) : Script Bytes Block Root 1 :=
  .ask [99] (fun _ => .done (fun _ => 0))
private def later (_ : RootCuts) : Script Bytes Block Unit 2 :=
  .ask [98] (fun _ => .ask [100] (fun _ => .abort))
private def fixture := continueRun (fun _ => zero) ⟨zero, FSFirstFresh.empty⟩ c1 c2 later
#guard fixture.1.isSome
#guard fixture.1.map Prod.snd == some none
#guard fixture.2.log.length == 10
#guard fixture.2.next == 7
#guard (fixture.2.log.map (·.fresh)).drop 8 == [false,true]
#guard (fixture.1.map (fun value => (c1Records value.1).length)) == some 1
#guard (fixture.1.map (fun value => (c2Records value.1).length)) == some 7

#print axioms extended_prefixes
#print axioms continued_prefix_answers
#print axioms continue_valid
#print axioms later_call_bound
end AspisV8Completion.FSAuthenticationSuffix
