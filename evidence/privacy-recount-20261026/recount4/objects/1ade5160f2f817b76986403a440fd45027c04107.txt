import R1Z.ProverRwOuterCaller
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwOuterGuardLeaves
open Aeneas Aeneas.Std Result ProverRwFull

def mask : Result U64 := .ok
  ProverRwRngNativeBody.aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1
def factor : Result U64 := .ok
  ProverRwRngNativeBody.aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1

theorem mask_source : mask = .ok 18003970557850322385#u64 := by unfold mask ProverRwRngNativeBody.aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1; rfl
theorem factor_source : factor = .ok 7605398817818846427#u64 := by unfold factor ProverRwRngNativeBody.aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1; rfl

variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  ProverRwOuterTag.selected {ops with op112 := mask,op113 := factor}

theorem mask_installed (ops : ExternalFuns) :
    @aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1 _
      (selected ops) = .ok 18003970557850322385#u64 := mask_source

theorem factor_installed (ops : ExternalFuns) :
    @aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1 _
      (selected ops) = .ok 7605398817818846427#u64 := factor_source

/-- Generic symbolic self-comparison, not enumeration of concrete bytes. -/
theorem list_compare_self (xs : List U8) :
    List.allM (fun xy : U8 × U8 => Result.ok (decide (¬ core.cmp.impls.PartialEqU8.ne xy.1 xy.2)))
      (xs.zip xs) = Result.ok true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [List.zip_cons_cons,List.allM] using ih

theorem array_ne_self {N : Usize} (a : Array U8 N) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a a = .ok false := by
  unfold core.array.equality.PartialEqArray.ne core.array.equality.PartialEqArray.eq
  simp only [ite_true,list_compare_self,bind_tc_ok]
  rfl

#print axioms mask_source
#print axioms factor_source
#print axioms mask_installed
#print axioms factor_installed
#print axioms list_compare_self
#print axioms array_ne_self
end R1Z.ProverRwOuterGuardLeaves
