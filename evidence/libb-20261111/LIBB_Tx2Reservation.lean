import LIB_Env
import NJC_FilledClause
set_option autoImplicit false
noncomputable section
namespace LIBB_Tx2Reservation
open Aeneas Aeneas.Std AspisR1
/-- A canonical discarded TryReserveError payload. Only its Err tag can be
observed by the frozen callers; no reservation success is fixed. -/
def failed : NP6_StdModel.ReserveError := ⟨.CapacityOverflow⟩
def reservation (env : RSL.Env) : NP6_StdModel.Reservation :=
 if env.reservation then .Ok () else .Err failed

theorem reserved (env : RSL.Env) : NJC_FilledClause.reserved (reservation env) = env.reservation := by
 cases h : env.reservation <;> simp only [reservation,h,Bool.false_eq_true,if_false,if_true,NJC_FilledClause.reserved]

theorem ok_iff (env : RSL.Env) : reservation env = .Ok () ↔ env.reservation = true := by
 cases h : env.reservation <;> simp only [reservation,h,Bool.false_eq_true,if_false,if_true,reduceCtorEq]

theorem filled64_root (env : RSL.Env) :
 NJC_FilledClause.native (reservation env) =
 CheckpointBytes3Allocation.filled env.reservation 64#usize
  (⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩ : NJC_FilledClause.K) := by
 rw [NJC_FilledClause.source,reserved]

/-- Connect the actual headline reservation binder without changing its Err
payload or assuming it succeeds. This is a runtime representation equality,
not a new caller-domain clause. -/
theorem actual_filled64 (env : RSL.Env) (actual : NP6_StdModel.Reservation)
 (bound : NJC_FilledClause.reserved actual = env.reservation) :
 NJC_FilledClause.native actual = NJC_FilledClause.native (reservation env) := by
 rw [NJC_FilledClause.source,NJC_FilledClause.source,bound,reserved]
#print axioms reserved
#print axioms ok_iff
#print axioms filled64_root
#print axioms actual_filled64
end LIBB_Tx2Reservation
end
