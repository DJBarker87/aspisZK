import LPq_WeightedStep
set_option autoImplicit false
namespace AspisR1.LPq_Weighted
open Aeneas Aeneas.Std Result LPi_FieldValues LPq_FieldPorts LPq_WeightedStep XRo_Join_Carriers

def run (k parts : Seven) : Nat → Usize → NE → Result NE
  | 0,_,sum => ok sum
  | n+1,i,sum => do
    let next ← step k parts sum i
    let j ← i+1#usize
    run k parts n j next

/-- Native seven-part weighting is linked one step at a time to XRy's already
installed indexed cohort fold. No independent weighted-sum equation is assumed. -/
theorem paired (n : Nat) (k parts : Seven) (hk : canonical k) (hp : canonical parts)
    (i : Usize) (sum : NE) (hs : canonE sum) (bound : i.val+n≤7) :
    ∃ out, run k parts n i sum=ok out ∧ canonE out ∧
      XRy_ClaimSumLoop.run (arr wide k) (arr wide parts) n i (wide sum)=ok (wide out) := by
  induction n generalizing i sum with
  | zero => exact ⟨sum,rfl,hs,rfl⟩
  | succ n ih =>
    have hi : i.val<7 := by omega
    obtain ⟨next,en,cn,rn⟩ := LPq_WeightedStep.paired k parts sum i hi hk hp hs
    obtain ⟨j,ej,hj⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
    have advance : j.val=i.val+1 := by simpa only [UScalar.ofNatCore_val_eq] using hj
    obtain ⟨out,eo,co,ro⟩ := ih j next cn (by omega)
    exact ⟨out,by rw [run,en,bind_tc_ok,ej,bind_tc_ok,eo],co,by
      rw [XRy_ClaimSumLoop.run,rn,bind_tc_ok,ej,bind_tc_ok,ro]⟩

theorem zero_canonical : canonE FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO := by
  norm_num [canonE,canonQ,canonC,LPi_CMProduct.Canon,
    FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.QM31.ZERO]

theorem zero_wide : wide FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=XRy_Powers.zero := by
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO FIo_Native.aspis_core.field.QM31.ZERO
  rfl

/-- SAME seven power and part arrays, complete native eight-word result and
concrete cohort sum. Uses the installed XRy sum theorem by Result uniqueness. -/
theorem source (k parts : Seven) (hk : canonical k) (hp : canonical parts) :
    ∃ out, run k parts 7 0#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok out ∧
      canonE out ∧
      AspisR1CurrentPreparedClaim.verifier.prepared_claim_sum
        (arr LPq_Powers.claim k) (arr LPq_Powers.claim parts)=ok (LPq_Powers.claim out) := by
  obtain ⟨out,en,co,rn⟩ := paired 7 k parts hk hp 0#usize _ zero_canonical (by decide)
  rw [zero_wide] at rn
  obtain ⟨actual,_,ra,rc⟩ := XRy_ClaimSum.sum (arr wide k) (arr wide parts)
    (canonical_port k hk) (canonical_port parts hp)
  have same : actual=wide out := Result.ok.inj (ra.symm.trans rn)
  rw [same] at rc
  refine ⟨out,en,co,?_⟩
  have maps (a : Seven) : arr AspisR1ClaimPreparedBridge.toClaimE (arr wide a)=arr LPq_Powers.claim a := by
    apply Subtype.ext
    change (a.val.map wide).map AspisR1ClaimPreparedBridge.toClaimE=a.val.map LPq_Powers.claim
    rw [List.map_map]
    rfl
  rw [maps,maps] at rc
  exact rc

#print axioms paired
#print axioms zero_canonical
#print axioms zero_wide
#print axioms source
end AspisR1.LPq_Weighted
