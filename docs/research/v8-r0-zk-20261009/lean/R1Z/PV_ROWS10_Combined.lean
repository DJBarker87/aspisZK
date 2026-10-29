import R1Z.PV_ROWS10_Entropy
import R1Z.PV_ROWS10_WorkRanges
set_option autoImplicit false
namespace R1Z.PV_ROWS10_Combined
open PV_ROWS10_Entropy PV_ROWS10_WorkRanges
/-- Combined accepted LOCAL statements. This deliberately does not assert any
native prefix binding, probe check, installed dictionary, fixture reachability,
OS distribution, or deployed privacy theorem. -/
theorem local_results (a b : List Reply) (ta tb da db : List UInt8)
    (publicControl : a.map control = b.map control)
    (publicLength : ta.length = tb.length) (n k : Nat) (hk : k < 16) :
    failed (run a ta da) = failed (run b tb db) ∧
    (buffer (run a ta da)).length = da.length + ta.length ∧
    start n k ≤ stop n k ∧ stop n k ≤ n ∧ stop n 15 = n := by
  exact ⟨public_control_suffices a b ta tb da db publicControl publicLength,
    buffer_length a ta da, (range_bounds n k hk).1,
    (range_bounds n k hk).2, end_last n⟩
#print axioms local_results
end R1Z.PV_ROWS10_Combined
