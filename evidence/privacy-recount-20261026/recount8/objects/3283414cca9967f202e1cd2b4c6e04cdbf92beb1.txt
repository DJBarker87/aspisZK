import R1Z.ProverRwP6PowersNativeStep
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6PowersNativeBridge
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6PowersNativeStep
open ProverRwP6PowersControl ProverRwP6PowersFinite
variable [ExternalTypes]
abbrev W := ProverRwFull.aspis_core.field.wide_exact.WideExact
-- Exact Result transport; the retained partial-fixpoint owner is traversed
-- symbolically with a decreasing byte counter, never concretely reduced.
theorem transport (ops : ExternalFuns) {N : Usize} (x : W) (fuel : Nat)
    (out : Array W N) (p : W) (i : Usize) (left : U8)
    (bound : i.val+fuel=N.val) (hl : left.val=fuel) :
    letI : ExternalFuns := dict ops
    ProverRwP6ResultMap.map (fun r => nativeArray (finish r))
      (finite x fuel out p i) =
    AspisR1ProducerRelease47.power_fill (nativeArray out) (toW x) (toW p) i left := by
  letI : ExternalFuns := dict ops
  induction fuel generalizing out p i left with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    have cap : ¬ i<N := by change ¬i.val<N.val; omega
    rw [AspisR1ProducerRelease47.power_fill,hz]
    simp only [finite,dispatch,cap,if_false,if_true,
      ProverRwP6ResultMap.map,ProverRwDictionaryTower.mapResult,finish]
  | succ fuel ih =>
    have hi : i.val<N.val := by omega
    have test : i<N := hi
    have hn : left≠0#u8 := by intro h; rw [h] at hl; change 0=fuel+1 at hl; omega
    obtain ⟨v,hr,hrn⟩ := ProverRwP6PowersNativeStep.read out i hi
    have add : (Usize.wrapping_add i 1#usize).val=i.val+1 := by
      rw [Usize.wrapping_add_val_eq]
      change (i.val+1)%UScalar.size .Usize=i.val+1
      apply Nat.mod_eq_of_lt
      have big := N.hSize
      omega
    by_cases last : fuel=0
    · subst fuel
      have one : left=1#u8 := by scalar_tac
      have stop : Usize.wrapping_add i 1#usize=N := UScalar.eq_of_val_eq (by rw [add]; omega)
      rw [AspisR1ProducerRelease47.power_fill]
      simp only [one,hn,if_false,hrn,bind_tc_ok,if_true,
        finite,dispatch,test,hr,stop,ProverRwP6ResultMap.map,
        ProverRwDictionaryTower.mapResult,finish]
      exact congrArg Result.ok (ProverRwP6PowersNativeStep.set out i p)
    · have more : left≠1#u8 := by intro h; rw [h] at hl; change 1=fuel+1 at hl; omega
      have nonstop : Usize.wrapping_add i 1#usize≠N := by
        intro h; have hv := congrArg UScalar.val h; rw [add] at hv; omega
      have dec : (U8.wrapping_sub left 1#u8).val=fuel := by
        rw [ProverCommitBasisCounter47.sub_one left (by omega)]
        omega
      obtain ⟨q,hq,hfull⟩ := ProverRwP6PowersNativeStep.mul ops p x
      have recur := ih (Aeneas.Std.Array.set out i p) (fromW q)
        (Usize.wrapping_add i 1#usize) (U8.wrapping_sub left 1#u8)
        (by rw [add]; omega) dec
      rw [AspisR1ProducerRelease47.power_fill]
      simp only [hn,if_false,hrn,bind_tc_ok,more,hq,lift,
        finite,dispatch,test,if_true,hr,nonstop,
        ProverRwFull.aspis_core.field.wide_exact.WideExact.mul,hfull]
      simp only [ProverRwP6PowersNativeStep.set,
        ProverRwDictionaryTower.native_w_roundtrip] at recur
      exact recur
#print axioms transport
end R1Z.ProverRwP6PowersNativeBridge
