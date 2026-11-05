import NHC_HintsTotal
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NHC_HintsTailFrame
/-- Arbitrary body bytes are framed. Only the final four values determine hints.
This is the emitted-body value law; native arbitrary-heap lifting is separate. -/
theorem suffix (whole : Slice U8) (pre : List U8) (a b c d : U8)
    (encoded : whole.val = pre ++ [a,b,c,d]) :
    ∃ body : Slice U8,
      NHC_Hints.pair_forest.split_pair_forest_terminal_bump_hints_v1 whole =
        ok (.Ok (body,⟨a,b,c,d⟩)) ∧ body.val = pre := by
  have lower : 4 ≤ whole.val.length := by simp [encoded]
  obtain ⟨body,hints,run,window,parts⟩ := NHC_HintsTotal.split whole lower
  have hb : body.val = pre := by
    rw [window,encoded]
    simp
  have tails : [hints.current_page,hints.next_page,hints.vault_authority,hints.vault_token_account] = [a,b,c,d] :=
    List.append_cancel_left (by simpa only [encoded,hb] using parts.symm)
  have hh : hints = ⟨a,b,c,d⟩ := by
    cases hints with
    | mk x0 x1 x2 x3 =>
      obtain ⟨h0,t1⟩ := List.cons.inj tails
      obtain ⟨h1,t2⟩ := List.cons.inj t1
      obtain ⟨h2,t3⟩ := List.cons.inj t2
      obtain ⟨h3,_⟩ := List.cons.inj t3
      cases h0
      cases h1
      cases h2
      cases h3
      rfl
  rw [hh] at run
  exact ⟨body,run,hb⟩
#print axioms suffix
end NHC_HintsTailFrame
