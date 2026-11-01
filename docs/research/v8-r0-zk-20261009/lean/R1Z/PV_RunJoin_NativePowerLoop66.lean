import R1Z.PV_RunJoin_NativePowerArray66
import PV_B1_PowersControl
import PV_B1_PowersBridge
import AspisR1ProducerRelease47.Powers48
import R1Z.ProverCommitBasisCounter47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativePowerLoop66
open Aeneas Aeneas.Std Result
open PV_RunJoin_NativePowerCarrier66 PV_RunJoin_NativePowerArray66
open PV_RunJoin_WeightMap46 (mapResult)
theorem complete {N : Usize} (x : W) (fuel : Nat) (out : Array W N)
    (p : W) (i : Usize) (left : U8) (bound : i.val+fuel=N.val) (hl : left.val=fuel) :
    mapResult image (PV_B1_PowersControl.finite x fuel out p i)=
      AspisR1ProducerRelease47.power_fill (image out) (toS x) (toS p) i left := by
  induction fuel generalizing out p i left with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    have stop : ¬i<N := by change ¬i.val<N.val;omega
    rw [AspisR1ProducerRelease47.power_fill,hz]
    simp only [PV_B1_PowersControl.finite,PV_B1_PowersControl.dispatch,stop,if_false,if_true]
    rfl
  | succ fuel ih =>
    have hi : i.val<N.val := by omega
    have test : i<N := hi
    have hn : left≠0#u8 := by intro h;rw [h] at hl;change 0=fuel+1 at hl;omega
    have inc := PV_B1_PowersBridge.step i test
    obtain ⟨v,hr,hrs⟩ := PV_RunJoin_NativePowerArray66.read out i hi
    by_cases last : fuel=0
    · subst fuel
      have one : left=1#u8 := by scalar_tac
      have stop : Usize.wrapping_add i 1#usize=N := UScalar.eq_of_val_eq (by rw [inc];omega)
      rw [AspisR1ProducerRelease47.power_fill]
      simp only [one,hn,if_false,hrs,bind_tc_ok,if_true,
        PV_B1_PowersControl.finite,PV_B1_PowersControl.dispatch,test,hr,stop,lt_self_iff_false]
      exact congrArg Result.ok (PV_RunJoin_NativePowerArray66.set out i p)
    · have more : left≠1#u8 := by intro h;rw [h] at hl;change 1=fuel+1 at hl;omega
      have nonstop : Usize.wrapping_add i 1#usize<N := by change (Usize.wrapping_add i 1#usize).val<N.val;rw [inc];omega
      have dec : (U8.wrapping_sub left 1#u8).val=fuel := by
        rw [ProverCommitBasisCounter47.sub_one left (by omega)];omega
      obtain ⟨z,hz,hzs⟩ := PV_RunJoin_NativePowerCarrier66.mul p x
      have recur := ih (Aeneas.Std.Array.set out i p) z (Usize.wrapping_add i 1#usize)
        (U8.wrapping_sub left 1#u8) (by rw [inc];omega) dec
      rw [AspisR1ProducerRelease47.power_fill]
      simp only [hn,if_false,hrs,bind_tc_ok,more,hzs,lift,
        PV_B1_PowersControl.finite,PV_B1_PowersControl.dispatch,test,if_true,hr,nonstop,hz]
      rw [PV_RunJoin_NativePowerArray66.set] at recur
      exact recur
#print axioms complete
end R1Z.PV_RunJoin_NativePowerLoop66
