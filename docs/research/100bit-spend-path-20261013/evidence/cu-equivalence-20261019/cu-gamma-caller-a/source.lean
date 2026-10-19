import CuSavingsGammaTable

/-! Consume the complete emitted preparation's computed-table invariant.
The context can perform accumulator allocation and all later tx1 operations,
including failing before consuming the table. This closes duplicate-compute
elimination after the new preparation; old/new claim factoring is separate. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsGammaCaller
open Aeneas Aeneas.Std Result AspisR1CuGamma
open CuSavingsGammaTable
variable [Boundaries]

def recomputing {H A : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) (initial : Table)
    (onError : Err → Result A) (context : Prepared → Result Table → Result A) : Result A := do
  let (result,_) ← gamma_new.Prepared.gamma_new_new D sem v hash initial
  match result with
  | .Err error => onError error
  | .Ok p => context p (weights.powers 29#usize p.gamma)

def retaining {H A : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) (initial : Table)
    (onError : Err → Result A) (context : Prepared → Result Table → Result A) : Result A := do
  let (result,g) ← gamma_new.Prepared.gamma_new_new D sem v hash initial
  match result with
  | .Err error => onError error
  | .Ok p => context p (.ok g)

theorem callers_eq {H A : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) (initial : Table)
    (onError : Err → Result A) (context : Prepared → Result Table → Result A) :
    recomputing D sem v hash initial onError context = retaining D sem v hash initial onError context := by
  unfold recomputing retaining
  cases h : gamma_new.Prepared.gamma_new_new D sem v hash initial with
  | fail e => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨result,g⟩
    cases result with
    | Err error => rfl
    | Ok p =>
      have hpow := source_success D sem v hash initial p g h
      simpa only [bind_tc_ok,uncurry_apply_pair] using congrArg (context p) hpow

#print axioms recomputing
#print axioms retaining
#print axioms callers_eq
end AspisR1.CuSavingsGammaCaller
