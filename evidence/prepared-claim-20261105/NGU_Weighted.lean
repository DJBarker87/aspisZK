import NGU_WeightedStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGU_Weighted
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_WeightedStep NGU_Carriers
open AspisR1CurrentPreparedClaim

def run (k parts : Seven) : Nat → Usize → NE → Result NE
 | 0,_,sum => ok sum
 | n+1,i,sum => do
   let next ← step k parts sum i
   let j ← i+1#usize
   run k parts n j next

/-- Finite induction through the emitted loop, with no assumed final sum. -/
theorem paired (n : Nat) (k parts : Seven) (hk : canonical k) (hp : canonical parts)
 (iter : NGU_WeightedStep.Range) (sum : NE) (hs : canonE sum)
 (hend : iter.end.val=7) (remaining : iter.start.val+n=7) :
 ∃ out, canonE out ∧ run k parts n iter.start sum=ok out ∧
 verifier.prepared_claim_sum_loop iter (arr NGU_Powers.claim k)
  (arr NGU_Powers.claim parts) (NGU_Powers.claim sum)=ok (NGU_Powers.claim out) := by
 induction n generalizing iter sum with
 | zero =>
   refine ⟨sum,hs,rfl,?_⟩
   apply NGU_Loop.done
   exact AspisR1CurrentPreparedClaim.sum_body_done _ _ iter (NGU_Powers.claim sum) (by omega)
 | succ n ih =>
   obtain ⟨iter',next,en,cn,hi,he,et⟩ := NGU_WeightedStep.paired k parts iter sum hend (by omega) hk hp hs
   obtain ⟨j,ej,hj⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=iter.start) (y:=1#usize) (by scalar_tac))
   have advance : j.val=iter.start.val+1 := by simpa only [UScalar.ofNatCore_val_eq] using hj
   have same : j=iter'.start := UScalar.eq_of_val_eq (advance.trans hi.symm)
   obtain ⟨out,co,eo,ro⟩ := ih iter' next cn (by rw [he];exact hend) (by omega)
   refine ⟨out,co,?_,?_⟩
   · rw [run,en,bind_tc_ok,ej,bind_tc_ok,same];exact eo
   · exact (NGU_Loop.cont _ _ _ et).trans ro

theorem zero_canonical : canonE FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO := by
 norm_num [canonE,canonQ,canonC,NFN_LPi_CMProduct.Canon,
  FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.QM31.ZERO]

theorem source (k parts : Seven) (hk : canonical k) (hp : canonical parts) :
 ∃ out, run k parts 7 0#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok out ∧
 canonE out ∧ verifier.prepared_claim_sum (arr NGU_Powers.claim k) (arr NGU_Powers.claim parts)=
  ok (NGU_Powers.claim out) := by
 obtain ⟨out,co,en,model⟩ := paired 7 k parts hk hp ⟨0#usize,7#usize⟩ _ zero_canonical rfl rfl
 refine ⟨out,en,co,?_⟩
 unfold verifier.prepared_claim_sum
 have zero : NGU_Powers.claim FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=
   aspis_core.field.WideExact.ZERO := by
    unfold FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
      FIo_Native.aspis_core.field.QM31.ZERO aspis_core.field.WideExact.ZERO aspis_core.field.QM31.ZERO
    rfl
 rw [←zero,model,bind_tc_ok]
 rfl

#print axioms paired
#print axioms zero_canonical
#print axioms source
end AspisR1.NGU_Weighted
end
