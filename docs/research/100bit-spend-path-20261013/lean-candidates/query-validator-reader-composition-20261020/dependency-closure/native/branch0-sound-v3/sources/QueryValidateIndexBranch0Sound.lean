import Aeneas
import QueryValidatorGeneratedPrefix
import QueryValidatorChunkNoHit
import QueryValidatorChunks12NoHit
import QueryValidateIndexBranch0
import QueryValidatorLoopInvariant
import Aeneas.Tactic.Solver.ScalarTac
open Aeneas Aeneas.Std Result AspisR1Stage2AdoptedResume
namespace AspisR1.QueryValidateIndexBranch0Sound
abbrev QueryArray := Array Std.U32 22#usize
open AspisR1.QueryValidatorChunkNoHit
open AspisR1.QueryValidatorLoopInvariant

theorem branch0_success_validAt
    (queries : QueryArray) (index : Usize)
    (hindex : index < 8#usize)
    (hsuccess : verifier.validate_query_index queries index =
      ok (core.result.Result.Ok ())) : validAt queries index := by
  have hcalls := AspisR1.QueryValidateIndexBranch0.branch0_calls_false queries index hindex hsuccess
  rcases hcalls with ⟨h0, h1, h2⟩
  have hindexNat : index.val < 8 := by simpa [UScalar.lt_equiv] using hindex
  have hbound : index.val < 22 := by omega
  unfold validAt
  constructor
  · exact hbound
  constructor
  · have hge : ¬ (queries.val[index.val]! ≥ 262144#u32) := by
      intro hbad
      have hcontr : ok (core.result.Result.Err verifier.Error.Checkpoint) =
          ok (core.result.Result.Ok ()) := by
        have hidx : Array.index_usize queries index = ok queries.val[index.val]! :=
          AspisR1.QueryValidatorChunkArrayBridge.index_ok_gen queries index (by scalar_tac)
        have hshift : (1#u32 <<< 18#i32) = ok (262144#u32) := by rfl
        simpa only [verifier.validate_query_index, hidx, hshift, bind_tc_ok, if_pos hbad]
          using hsuccess
      cases hcontr
    have hnat : (queries.val[index.val]!).val < 2 ^ 18 := by
      by_contra hn
      have hle : (262144 : Nat) ≤ (queries.val[index.val]!).val := by
        norm_num at hn
        have hbound : index.val < queries.val.length := by scalar_tac
        simpa only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hbound] using hn
      have hge' : (queries.val[index.val]!) ≥ 262144#u32 := by
        have hle' : (262144#u32).val ≤ (queries.val[index.val]!).val := by simpa using hle
        exact (UScalar.le_equiv _ _).2 hle'
      exact hge hge'
    exact hnat
  · intro j hj
    have hj8 : j < 8 := by omega
    have hjcase : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    have hno := AspisR1.QueryValidatorChunkNoHit.chunk0_nohit
      queries (queries.val[index.val]!) index h0
    rcases hjcase with hj0 | hjcase
    · subst j
      have hc : (index > 0#usize) = true := by scalar_tac
      have hneq := hno.1 hc
      intro heq
      apply hneq
      apply UScalar.val_eq_imp
      simpa [queryValue] using heq
    · rcases hjcase with hj1 | hjcase
      · subst j
        have hc : (index > 1#usize) = true := by scalar_tac
        have hneq := hno.2.1 hc
        intro heq
        apply hneq
        apply UScalar.val_eq_imp
        simpa [queryValue] using heq
      · rcases hjcase with hj2 | hjcase
        · subst j
          have hc : (index > 2#usize) = true := by scalar_tac
          have hneq := hno.2.2.1 hc
          intro heq
          apply hneq
          apply UScalar.val_eq_imp
          simpa [queryValue] using heq
        · rcases hjcase with hj3 | hjcase
          · subst j
            have hc : (index > 3#usize) = true := by scalar_tac
            have hneq := hno.2.2.2.1 hc
            intro heq
            apply hneq
            apply UScalar.val_eq_imp
            simpa [queryValue] using heq
          · rcases hjcase with hj4 | hjcase
            · subst j
              have hc : (index > 4#usize) = true := by scalar_tac
              have hneq := hno.2.2.2.2.1 hc
              intro heq
              apply hneq
              apply UScalar.val_eq_imp
              simpa [queryValue] using heq
            · rcases hjcase with hj5 | hjcase
              · subst j
                have hc : (index > 5#usize) = true := by scalar_tac
                have hneq := hno.2.2.2.2.2.1 hc
                intro heq
                apply hneq
                apply UScalar.val_eq_imp
                simpa [queryValue] using heq
              · rcases hjcase with hj6 | hj7
                · subst j
                  have hc : (index > 6#usize) = true := by scalar_tac
                  have hneq := hno.2.2.2.2.2.2.1 hc
                  intro heq
                  apply hneq
                  apply UScalar.val_eq_imp
                  simpa [queryValue] using heq
                · subst j
                  have hc : (index > 7#usize) = true := by scalar_tac
                  have hneq := hno.2.2.2.2.2.2.2 hc
                  intro heq
                  apply hneq
                  apply UScalar.val_eq_imp
                  simpa [queryValue] using heq

#print axioms branch0_success_validAt
end AspisR1.QueryValidateIndexBranch0Sound
