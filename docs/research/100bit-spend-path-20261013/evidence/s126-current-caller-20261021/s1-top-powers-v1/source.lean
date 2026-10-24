import S1TopPrepareSourceV1
set_option autoImplicit false
namespace AspisS1TopPowers
open Aeneas Aeneas.Std Result
open AspisS1TopPrepareCarrier AspisR1ClaimPreparedBridge
open AspisR1CurrentCaller.InstalledPreparation
open AspisR1CurrentPreparedClaim

/-- Full eight-word carrier maps. No reduction modulo p occurs here. -/
def claimE (x : Top.E) : Concrete.E := toClaimE (retainedE (fromE x))
def topE (x : Concrete.E) : Top.E := toE (currentE (fromClaimE x))
@[simp] theorem claim_top (x : Concrete.E) : claimE (topE x)=x := rfl
@[simp] theorem top_claim (x : Top.E) : topE (claimE x)=x := rfl

/-- The existing proved early-return powers candidate at the complete op17
ABI. Native adoption/equivalence and frozen re-pin remain separate gates. -/
def powers (N : Usize) (x : Top.E) : Result (Array Top.E N) := do
  let out ← ClaimPowers.powers N (claimE x)
  ok (mapArray topE out)

def install (base : VTop_Stages.Ops) : VTop_Stages.Ops := {base with op17:=powers}

/-- TOTAL on canonical input, with every returned cell canonical and equal to
its mathematical power. This source procedure has no digest/observer child. -/
theorem powers_total_exact (N : Usize) (x : Top.E) (canonical : Concrete.Canonical (claimE x)) :
    ∃ out, powers N x=ok out ∧ ∀ j : Fin N.val,
      Concrete.Canonical (claimE (out.val[j.val]'(by rw [out.property]; exact j.isLt))) ∧
      Concrete.decode (claimE (out.val[j.val]'(by rw [out.property]; exact j.isLt)))=
        Concrete.decode (claimE x)^j.val := by
  obtain ⟨out,run,exactCells⟩ := ClaimPowers.powers_total_exact N (claimE x) canonical
  refine ⟨mapArray topE out,?_,?_⟩
  · simp only [powers,run,bind_tc_ok]
  · intro j
    simpa only [mapArray,List.getElem_map,claim_top] using exactCells j

/-- The SAME successful op17 return, not a separately chosen total result. -/
theorem installed_return (base : VTop_Stages.Ops) (N : Usize) (x : Top.E)
    (out : Array Top.E N) (canonical : Concrete.Canonical (claimE x))
    (success : (install base).op17 N x=ok out) :
    ∀ j : Fin N.val,
      Concrete.Canonical (claimE (out.val[j.val]'(by rw [out.property]; exact j.isLt))) ∧
      Concrete.decode (claimE (out.val[j.val]'(by rw [out.property]; exact j.isLt)))=
        Concrete.decode (claimE x)^j.val := by
  obtain ⟨actual,run,cells⟩ := powers_total_exact N x canonical
  change powers N x=ok out at success
  rw [run] at success
  cases Result.ok.inj success
  exact cells

#print axioms claim_top
#print axioms top_claim
#print axioms powers_total_exact
#print axioms installed_return
end AspisS1TopPowers
