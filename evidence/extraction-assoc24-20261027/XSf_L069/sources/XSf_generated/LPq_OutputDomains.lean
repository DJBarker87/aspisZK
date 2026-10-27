import LPq_Weighted
import LPm_PowersBridge
set_option autoImplicit false
namespace AspisR1.LPq_OutputDomains
open Aeneas Aeneas.Std Result LPi_FieldValues LPm_RawPort

theorem finish (s : Native) : ∃ out,
    FIo_Native.fast_pairing.EbyKDot.finish s=ok out ∧ canonE out := by
  obtain ⟨out,run,h0,h1,h2,h3,h4,h5,h6,h7⟩ := LPf_PublicDotAllStates.source s
  refine ⟨out,run,?_⟩
  change ((out.c0.c0.a.val<2147483647 ∧ out.c0.c0.b.val<2147483647) ∧
    (out.c0.c1.a.val<2147483647 ∧ out.c0.c1.b.val<2147483647)) ∧
    ((out.c1.c0.a.val<2147483647 ∧ out.c1.c0.b.val<2147483647) ∧
    (out.c1.c1.a.val<2147483647 ∧ out.c1.c1.b.val<2147483647))
  rw [h0,h1,h2,h3,h4,h5,h6,h7]
  exact ⟨⟨⟨Nat.mod_lt _ (by decide),Nat.mod_lt _ (by decide)⟩,
    ⟨Nat.mod_lt _ (by decide),Nat.mod_lt _ (by decide)⟩⟩,
    ⟨⟨Nat.mod_lt _ (by decide),Nat.mod_lt _ (by decide)⟩,
    ⟨Nat.mod_lt _ (by decide),Nat.mod_lt _ (by decide)⟩⟩⟩

theorem point {H : Type} {sem : AspisR1CurrentPreparedClaim.r1_semantic.Verified H}
    {y1 : Slice U8} {g : Array AspisR1CurrentPreparedClaim.Concrete.E 29#usize}
    {p : Usize} {iter : LPm_PointLoop.Range} {s : Native} {xs : List (NE×NQ)} {out : NE}
    (tr : LPm_PointLoop.Trace sem y1 g p iter s xs out) : canonE out := by
  induction tr with
  | done iter iter' s out next run =>
    obtain ⟨actual,call,ca⟩ := finish s
    have same : actual=out := Result.ok.inj (call.symm.trans run)
    simpa only [same] using ca
  | step l v q next read weight cv cq count push tail ih => exact ih

theorem powers {N : Usize} (x : NE) (hx : canonE x) (a : Array NE N)
    (run : FIo_Native.weights.powers N x=ok a) : ∀ z ∈ a.val, canonE z := by
  obtain ⟨actual,call,holds⟩ := LPi_PowersSource.source N x hx
  have same : actual=a := Result.ok.inj (call.symm.trans run)
  subst actual
  intro z hz
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hz
  have bound : i<N.val := by rw [←a.property]; exact hi
  obtain ⟨v,hv,cv,_⟩ := holds i bound
  rw [List.getElem?_eq_getElem hi] at hv
  exact (Option.some.inj hv) ▸ cv

#print axioms finish
#print axioms point
#print axioms powers
end AspisR1.LPq_OutputDomains
