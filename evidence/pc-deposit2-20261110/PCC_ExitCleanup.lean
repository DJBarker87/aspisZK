import PCA_GuardSteps
set_option autoImplicit false
namespace PCC
open PCA
/-- Exact lane cleanup when page acquisition failed: the page guard was
never pushed. This is a model component, not a native Err-path certificate. -/
theorem error_cleanup_one (s : PCA_State) (events : List PCA_Event)
    (lane : NLF_RefCell.Guard) (e : Failure) (stack : s.liveGuards = [lane]) :
    (finish ⟨s,events,.error e⟩).events =
      events ++ [.token (.release lane (NLF_ParentModel.release s.loans lane).2),
        .returned (.error e)] := by
  simp only [finish, stack, cleanup, List.append_assoc, List.cons_append, List.nil_append]

/-- Non-returning aborts retain the complete loan state and guard stack. -/
theorem abort_guard_frame (r : Execution Unit) (why : String) (h : r.reply = .abort why) :
    (finish r).state.liveGuards = r.state.liveGuards ∧
    (finish r).state.loans = r.state.loans := by
  simp [finish,h]
#print axioms error_cleanup_one
#print axioms abort_guard_frame
end PCC
