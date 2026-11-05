import NGL_CloneDomain
set_option autoImplicit false
namespace NGL_LengthCarrier
open Aeneas Aeneas.Std Result
abbrev R := core.result.Result Usize AdapterRw.solana_program_error.ProgramError
structure Observation where
  tag : Usize
  value : Usize
  deriving DecidableEq

def domain (r : R) : Prop :=
  (∃ n, r = .Ok n) ∨ r = .Err .AccountBorrowFailed ∨ r = .Err .InvalidAccountData

def observe : R → Observation
  | .Ok n => ⟨0#usize,n⟩
  | .Err .AccountBorrowFailed => ⟨1#usize,0#usize⟩
  | .Err .InvalidAccountData => ⟨2#usize,0#usize⟩
  | .Err _ => ⟨3#usize,0#usize⟩

theorem domain_iff (r : R) : domain r ↔ (observe r).tag.val < 3 := by
  cases r with
  | Ok n => simp [domain,observe]
  | Err e => cases e <;> simp [domain,observe]

/-- The observation's tag check supplies the native-domain fact itself. -/
theorem domain_of_observe (r s : R) (sd : domain s) (same : observe r = observe s) : domain r := by
  apply (domain_iff r).mpr
  rw [congrArg (fun o => o.tag.val) same]
  exact (domain_iff s).mp sd

/-- Complete-result recovery on the caller-produced error domain. The String
    variant is excluded explicitly, never silently collapsed to the same tag. -/
theorem injective_on_domain (r s : R) (rd : domain r) (sd : domain s)
    (same : observe r = observe s) : r = s := by
  rcases rd with ⟨n,rfl⟩ | rfl | rfl <;>
    rcases sd with ⟨m,rfl⟩ | rfl | rfl <;>
    simp_all [observe,Observation.mk.injEq]

/-- The actual model result is determined by the observation, without a supplied
    transaction result, accepted execution or endpoint-equality hypothesis. -/
theorem recovered (ops : AdapterRw.Ops) (a : NGL_CloneDomain.Account) (native : R)
    (inputDomain : domain a.length)
    (observed : observe native = observe a.length) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len (NGL_CloneDomain.install ops) a =
      ok native := by
  rw [NGL_CloneDomain.length_result]
  rw [injective_on_domain native a.length (domain_of_observe native a.length inputDomain observed) inputDomain observed]
#print axioms domain_iff
#print axioms domain_of_observe
#print axioms injective_on_domain
#print axioms recovered
end NGL_LengthCarrier
