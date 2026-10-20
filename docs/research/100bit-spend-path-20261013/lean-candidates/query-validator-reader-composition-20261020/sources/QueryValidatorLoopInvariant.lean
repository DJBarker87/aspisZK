import Aeneas
import QueryValidatorGeneratedPrefix
import Aeneas.Tactic.Solver.ScalarTac
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2AdoptedResume

namespace AspisR1.QueryValidatorLoopInvariant

abbrev QueryArray := Array Std.U32 22#usize

def queryValue (queries : QueryArray) (i : Nat) : Nat := (queries.val[i]!).val

def validAt (queries : QueryArray) (i : Usize) : Prop :=
  i.val < 22 ∧ queryValue queries i.val < 2 ^ 18 ∧
    ∀ j : Nat, j < i.val → queryValue queries j ≠ queryValue queries i.val

def indexCheckOK (queries : QueryArray) (i : Usize) : Prop :=
  verifier.validate_query_index queries i = ok (core.result.Result.Ok ())

def loopInvariant (queries : QueryArray) (s : Usize × Bool) : Prop :=
  s.1.val ≤ 22 ∧
    (s.2 = true → ∀ i : Usize, i.val < s.1.val → indexCheckOK queries i)

theorem validate_loop_success_sound
    (queries : QueryArray)
    (htotal : ∀ i : Usize, i.val < 22 →
      ∃ r, verifier.validate_query_index queries i = ok r)
    (hcheck : ∀ i : Usize, i.val < 22 → indexCheckOK queries i → validAt queries i)
    (hloop : verifier.validate_queries_loop queries 0#usize true = ok true) :
    ∀ i : Usize, i.val < 22 → validAt queries i := by
  have hwp : WP.spec (verifier.validate_queries_loop queries 0#usize true)
      (fun out => out = true → ∀ i : Usize, i.val < 22 → validAt queries i) := by
    unfold verifier.validate_queries_loop
    refine loop.spec_decr_nat
      (fun s : Usize × Bool => 22 - s.1.val)
      (loopInvariant queries)
      (fun out => out = true → ∀ i : Usize, i.val < 22 → validAt queries i)
      (fun s => verifier.validate_queries_loop.body queries s.1 s.2)
      (0#usize, true) ?_ ?_
    · rintro ⟨index, valid⟩ ⟨hindex, hvalid⟩
      change index.val ≤ 22 at hindex
      change (valid = true → ∀ i : Usize, i.val < index.val → indexCheckOK queries i) at hvalid
      by_cases hlt : index < 22#usize
      · have hltNat : index.val < 22 := by simpa [UScalar.lt_equiv] using hlt
        have hadd : index + 1#usize ⦃ j => j.val = index.val + 1 ⦄ := by
          apply Usize.add_spec
          scalar_tac
        obtain ⟨nextIndex, hnext, hnextVal⟩ := WP.spec_imp_exists hadd
        change nextIndex.val = index.val + 1 at hnextVal
        obtain ⟨result, hcall⟩ := htotal index hltNat
        cases result with
        | Ok unit =>
          cases unit
          have hbody : verifier.validate_queries_loop.body queries index valid =
              ok (cont (nextIndex, valid)) := by
            simp [verifier.validate_queries_loop.body, hlt, hcall, hnext]
          rw [hbody, WP.spec_ok]
          simp only [loopInvariant, Prod.fst, Prod.snd]
          constructor
          · constructor
            · omega
            · intro hvalidNext
              intro i hi
              have hiLt : i.val < index.val + 1 := by simpa [hnextVal] using hi
              by_cases hltOld : i.val < index.val
              · exact hvalid hvalidNext i hltOld
              · have heq : i.val = index.val := by omega
                have hiEq : i = index := UScalar.val_eq_imp i index (by simpa using heq)
                subst i
                exact hcall
          · change 22 - nextIndex.val < 22 - index.val
            omega
        | Err err =>
          have hbody : verifier.validate_queries_loop.body queries index valid =
              ok (cont (nextIndex, false)) := by
            simp [verifier.validate_queries_loop.body, hlt, hcall, hnext]
          rw [hbody, WP.spec_ok]
          simp only [loopInvariant, Prod.fst, Prod.snd]
          constructor
          · constructor
            · omega
            · intro hfalse
              cases hfalse
          · change 22 - nextIndex.val < 22 - index.val
            omega
      · have hbody : verifier.validate_queries_loop.body queries index valid = ok (done valid) := by
          simp [verifier.validate_queries_loop.body, hlt]
        rw [hbody, WP.spec_ok]
        intro hv
        have hindexEq : index.val = 22 := by
          have hnlt : ¬ index.val < 22 := by simpa [UScalar.lt_equiv] using hlt
          omega
        intro i hi
        have hi22 : i.val < 22 := hi
        exact hcheck i hi22 (hvalid hv i (by omega))
    · constructor
      · simp
      · intro htrue i hi
        simp at hi
  obtain ⟨out, hout, hpost⟩ := WP.spec_imp_exists hwp
  rw [hloop] at hout
  injection hout with hout
  subst out
  exact hpost rfl

theorem validate_queries_success_sound
    (queries : QueryArray)
    (htotal : ∀ i : Usize, i.val < 22 →
      ∃ r, verifier.validate_query_index queries i = ok r)
    (hcheck : ∀ i : Usize, i.val < 22 → indexCheckOK queries i → validAt queries i)
    (hvalidate : verifier.validate_queries queries = ok (core.result.Result.Ok ())) :
    ∀ i : Usize, i.val < 22 → validAt queries i := by
  unfold verifier.validate_queries at hvalidate
  cases hloop : verifier.validate_queries_loop queries 0#usize true with
  | ok valid =>
    simp [hloop] at hvalidate
    have hv : valid = true := by cases valid <;> simp_all
    have hrun : verifier.validate_queries_loop queries 0#usize true = ok true := by
      simpa [hloop, hv]
    exact validate_loop_success_sound queries htotal hcheck hrun
  | fail e => simp [hloop] at hvalidate
  | div => simp [hloop] at hvalidate

end AspisR1.QueryValidatorLoopInvariant
