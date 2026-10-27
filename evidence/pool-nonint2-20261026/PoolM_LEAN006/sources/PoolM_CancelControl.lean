import PoolM_CancelGuard
set_option autoImplicit false
namespace PoolM_CancelControl
open Aeneas Aeneas.Std Result PoolM_Owned PoolM_CancelGuard

theorem prepared_cases (a : Account) (size : Usize) :
    prepared a size = ok 0#u32 ∨ prepared a size = ok 1#u32 := by
  by_cases hlen : a.len = size <;>
    cases ho : a.owner_matches <;> cases he : a.executable <;>
    cases hs : a.signer <;> cases hw : a.writable <;>
    simp [prepared,ho,he,hs,hw,hlen]

theorem authority_cases (a : Account) :
    authority a = ok 0#u32 ∨ authority a = ok 2#u32 := by
  cases hs : a.signer <;> cases hw : a.writable <;>
    cases he : a.executable <;> cases ho : a.system_owned <;>
    simp [authority,hs,hw,he,ho]

/-- Inversion of the complete extracted role-control prefix. Early errors are
not replaced by success; the optional shard is checked only on its live arm. -/
theorem accepted_roles (payer core shard : Account) (hasShard : Bool) :
    cancel_roles payer core shard hasShard = ok 0#u32 ↔
    authority payer = ok 0#u32 ∧ prepared core 10000#usize = ok 0#u32 ∧
      (hasShard = true → prepared shard 8504#usize = ok 0#u32) := by
  rcases authority_cases payer with hp | hp <;>
    rcases prepared_cases core 10000#usize with hc | hc <;>
    rcases prepared_cases shard 8504#usize with hs | hs <;>
    cases hasShard <;> simp [cancel_roles,hp,hc,hs]

/-- An occupied retained checkpoint cannot occupy either plan role on an
accepted control path. This is a reference theorem; native guard/refinement
and physical account association are separate evidence obligations. -/
theorem occupied_plans (payer core shard : Account) (hasShard : Bool)
    (accepted : cancel_roles payer core shard hasShard = ok 0#u32) :
    (core.len.val ≠ 192 ∧ core.len.val ≠ 1768) ∧
      (hasShard = true → shard.len.val ≠ 192 ∧ shard.len.val ≠ 1768) := by
  obtain ⟨_,hc,hs⟩ := (accepted_roles payer core shard hasShard).mp accepted
  have cc := ((prepared_ok core 10000#usize).mp hc).2.2.2.2
  constructor
  · constructor <;> scalar_tac
  · intro live
    have ss := ((prepared_ok shard 8504#usize).mp (hs live)).2.2.2.2
    constructor <;> scalar_tac

/-- Both possible occupied-account owners are non-System in the runtime
instance. The explicit boolean tests that instance, not an axiom of keys. -/
theorem occupied_authority (payer core shard : Account) (hasShard : Bool)
    (foreign : payer.system_owned = false) :
    cancel_roles payer core shard hasShard = ok 2#u32 := by
  simp [cancel_roles,authority_foreign payer foreign]

#print axioms prepared_cases
#print axioms authority_cases
#print axioms accepted_roles
#print axioms occupied_plans
#print axioms occupied_authority
end PoolM_CancelControl
