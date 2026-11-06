import PCA_Borrow
import NLF_CounterLaws
set_option autoImplicit false
namespace PCA
open NLF_RefCell NLF_SdkModel

theorem exclusive_release_result (s : State) (g : Guard)
    (kind : g.kind = .exclusive) (valid : Valid (s.cells g.cell))
    (token : live (s.cells g.cell) g.token .exclusive) :
    release s g = .ok (put s g.cell {s.cells g.cell with writer := none}) := by
  simp only [release, kind, (exclusive_drop_valid (s.cells g.cell) g.token valid token).1]

theorem exclusive_release_zero (s : State) (g : Guard)
    (valid : Valid (s.cells g.cell)) (token : live (s.cells g.cell) g.token .exclusive) :
    flag ((put s g.cell {s.cells g.cell with writer := none}).cells g.cell) = 0 := by
  rw [put_same]
  exact NLF_CounterLaws.exclusive_zero _ g.token valid token

/-- Reverse lexical cleanup order, including observed release errors. Legal
release of BOTH actual guards still needs caller/child token preservation. -/
theorem cleanup_two_order (s : PCA_State) (page lane : Guard) :
    (cleanup [page,lane] s).2 =
      [.token (.release page (NLF_ParentModel.release s.loans page).2),
       .token (.release lane (NLF_ParentModel.release (NLF_ParentModel.release s.loans page).1 lane).2)] := rfl

theorem abort_keeps_loans (r : Execution Unit) (why : String) (abort : r.reply = .abort why) :
    (finish r).state.loans = r.state.loans ∧
    (finish r).events = r.events ++ [.aborted why] := by
  simp [finish, abort]

#print axioms exclusive_release_result
#print axioms exclusive_release_zero
#print axioms cleanup_two_order
#print axioms abort_keeps_loans
end PCA
