import RPu_FIr_ArrayRead
import RPu_FIq_Native14
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_SelectedClaim
open Aeneas Aeneas.Std Result FIq_Native
open FIr_NativeValue (Canon decode K)
abbrev NQ := field.QM31

theorem reached (claims : Array NQ 84#usize) (point column : Usize) (out : NQ)
    (run : pool_v1.pair_forest_semantic_terminal.selected_claim claims point column=ok out) :
    out∈claims.val := by
  unfold pool_v1.pair_forest_semantic_terminal.selected_claim at run
  obtain ⟨width,hw,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨base,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨index,hi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  exact FIr_ArrayRead.member claims index out run

theorem canonical (claims : Array NQ 84#usize) (point column : Usize) (out : NQ)
    (all : ∀ x∈claims.val,Canon x)
    (run : pool_v1.pair_forest_semantic_terminal.selected_claim claims point column=ok out) : Canon out :=
  all out (reached claims point column out run)

#print axioms reached
#print axioms canonical
end AspisR1.FIr_SelectedClaim
end
