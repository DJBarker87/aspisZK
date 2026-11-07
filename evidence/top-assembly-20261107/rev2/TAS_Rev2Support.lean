/-
TAS_Rev2Support: the two inversion facts that the RSL Revision 2 repairs of
NNC_RSLReads and NNC_RSLAuth need (TAS_G0_BRIEF.md section 3).

Target not yet established.  Core Lean plus RSL_ (Revision 2) and
NMV_RslLaws.bind_return only.  No sorry, no axiom declaration.  These are
statements about RSL definitions; they prove no row.
-/
import NMV_RslLaws
set_option autoImplicit false

namespace RSL.TASRev2
open RSL

/-- An RS bind that returned `ok` ran its first step to an `ok`. -/
theorem rsbind_ok {α β : Type} (m : RS α) (k : α → RS β) (env : Env) (b : β)
    (es : List Event) (h : RS.bind m k env ⟨.ret (.ok b), es⟩) :
    ∃ a e1 e2, m env ⟨.ret (.ok a), e1⟩ ∧ k a env ⟨.ret (.ok b), e2⟩ ∧ es = e1 ++ e2 := by
  obtain ⟨r, e1, e2, hm, hk, he⟩ := NMV_RslLaws.bind_return _ _ _ _ _ h
  cases r with
  | ok a => exact ⟨a, e1, e2, hm, hk, he⟩
  | error e =>
    simp only [Spec.pure, Obs.mk.injEq, Exit.ret.injEq] at hk
    cases hk.1

/-- Revision 2 getter inversion (replaces `ofExcept_return` at an
`OwnedAccount.data`/`data_len` site): an `ok` return of the clone-armed read
means the stored value was `ok` with that payload. -/
theorem ofCloned_return {α : Type} (x : Except ProgramError α) (env : Env) (a : α)
    (es : List Event) (h : RS.ofCloned x env ⟨.ret (.ok a), es⟩) : x = .ok a := by
  cases x with
  | ok v =>
    simp only [RS.ofCloned, RS.pure, Spec.pure, Obs.mk.injEq, Exit.ret.injEq,
      Except.ok.injEq] at h
    rw [h.1]
  | error e =>
    simp only [RS.ofCloned] at h
    split at h
    · obtain ⟨_, _, _, _, hk, _⟩ := rsbind_ok _ _ _ _ _ h
      simp only [RS.throw, Spec.pure, Obs.mk.injEq, Exit.ret.injEq] at hk
      cases hk.1
    · simp only [RS.throw, Spec.pure, Obs.mk.injEq, Exit.ret.injEq] at h
      cases h.1

theorem data_return (x : OwnedAccount) (env : Env) (d : Bytes) (es : List Event)
    (h : x.data env ⟨.ret (.ok d), es⟩) : x.bytes = .ok d :=
  ofCloned_return _ _ _ _ h

/-- Revision 2 `mapVErr` (TX2:241, with the `format!` allocation): an Err
reply never returns `ok`, so an accepted suffix had an `ok` reply. -/
theorem mapVErr241_error_not_ok (V : TX2_241.V2Lib) (e : V.VErr) (env : Env) (u : Unit)
    (es : List Event) : ¬ TX2_241.mapVErr V (.error e) env ⟨.ret (.ok u), es⟩ := by
  intro h
  unfold TX2_241.mapVErr at h
  obtain ⟨_, _, _, _, h2, _⟩ := rsbind_ok _ _ _ _ _ h
  obtain ⟨_, _, _, _, h3, _⟩ := rsbind_ok _ _ _ _ _ h2
  simp only [RS.throw, Spec.pure, Obs.mk.injEq, Exit.ret.injEq] at h3
  cases h3.1

#print axioms rsbind_ok
#print axioms ofCloned_return
#print axioms data_return
#print axioms mapVErr241_error_not_ok

end RSL.TASRev2
