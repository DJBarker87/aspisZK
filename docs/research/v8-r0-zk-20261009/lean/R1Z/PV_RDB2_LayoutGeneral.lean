import R1Z.PV_RDB2_LayoutRepeat

/-! The repeat algorithms genuinely differ on unpadded layouts. This is a
restated before/after law, not an unconditional equivalence assertion. RawVec
uses real-type layouts, whose padded size equals size. -/
namespace R1Z.PV_RDB2_LayoutGeneral
set_option autoImplicit false
open PV_RDB2_Layout

def historical (limit size stride : Nat) : Nat → Option Nat
  | 0 => checked limit 0
  | n+1 => (checked limit (n*stride)).bind (fun bytes => checked limit (bytes+size))

def deployed (limit stride count : Nat) : Option Nat := checked limit (count*stride)

theorem historical_closed (limit size stride n : Nat) :
    historical limit size stride (n+1) = checked limit (n*stride+size) := by
  by_cases h : n*stride+size ≤ limit
  · have hp : n*stride ≤ limit := by omega
    simp only [historical,checked,h,hp,if_true,Option.bind_some]
  · by_cases hp : n*stride ≤ limit
    · simp only [historical,checked,h,hp,if_false,if_true,Option.bind_some]
    · simp only [historical,checked,h,hp,if_false,Option.bind_none]

theorem before_success (limit size stride n : Nat) :
    historical limit size stride (n+1) = some (n*stride+size) ↔
      n*stride+size ≤ limit := by
  rw [historical_closed]
  simp only [checked]
  split <;> simp_all

theorem after_success (limit stride count : Nat) :
    deployed limit stride count = some (count*stride) ↔ count*stride ≤ limit := by
  unfold deployed checked
  split <;> simp_all

theorem before_after_size (size stride n : Nat) (padded : size ≤ stride) :
    (n+1)*stride = (n*stride+size)+(stride-size) := by
  rw [Nat.add_mul]
  simp only [Nat.one_mul]
  omega

theorem padded_complete (limit size count : Nat) :
    historical limit size size count = deployed limit size count := by
  exact PV_RDB2_Layout.same_result limit size count

/-- Checked source-level witness to why the generic theorem must retain its
padded-layout domain. This is not a counterexample for a real-type RawVec. -/
theorem unpadded_results :
    historical 7 1 8 1 = some 1 ∧ deployed 7 8 1 = none := by
  constructor <;> rfl

#print axioms historical_closed
#print axioms before_success
#print axioms after_success
#print axioms before_after_size
#print axioms padded_complete
#print axioms unpadded_results
end R1Z.PV_RDB2_LayoutGeneral
