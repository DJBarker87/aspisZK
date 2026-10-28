import R1Z.PV_RunJoin_WeightPowersThread47
import AspisR1ProducerRelease47.Powers48
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPowersLoop47
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightWide46 (E toWide)
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult)

theorem complete {N : Usize} (x p : E) (out : Array E N) (n : Nat)
    (i : Usize) (left : U8) (hl : left.val=n) (hb : i.val+n=N.val) :
    AspisR1ProducerRelease47.power_fill (amap toWide out) (toWide x) (toWide p) i left=
      mapResult (amap toWide) (PV_B2_251c1.prover_powers.powers_loop x out p i) := by
  induction n generalizing i left out p with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    have hi : ¬i<N := by scalar_tac
    rw [PV_B2_C_PowersTotal.done x out p i hi,hz,AspisR1ProducerRelease47.power_fill]
    rfl
  | succ n ih =>
    have hi : i<N := by scalar_tac
    have hv : (Usize.wrapping_add i 1#usize).val=i.val+1 := PV_B2_C_PowersBody.next_val i hi
    obtain ⟨old,hr⟩ := PV_RunJoin_WeightPowersThread47.read out i hi
    have hread : Array.index_usize (amap toWide out) i=ok (toWide old) := by
      rw [PV_RunJoin_WeightMap46.index,hr];rfl
    by_cases hn : n=0
    · subst n
      have hone : left=1#u8 := by scalar_tac
      have hm : ¬Usize.wrapping_add i 1#usize<N := by scalar_tac
      rw [PV_RunJoin_WeightPowersThread47.last x p out i hi hm,hone,
        AspisR1ProducerRelease47.power_fill]
      simp only [if_false,if_true,Array.index_mut_usize,hread,bind_tc_ok]
      change ok (Aeneas.Std.Array.set (amap toWide out) i (toWide p))=
        ok (amap toWide (Aeneas.Std.Array.set out i p))
      rw [PV_RunJoin_WeightBorrow46.restore]
    · have hzero : left≠0#u8 := by scalar_tac
      have hone : left≠1#u8 := by scalar_tac
      have hm : Usize.wrapping_add i 1#usize<N := by scalar_tac
      have hd : (U8.wrapping_sub left 1#u8).val=n := by
        rw [U8.wrapping_sub_val_eq,UScalar.size]
        change (left.val+255)%256=n
        have hbounds := left.hBounds
        change left.val<256 at hbounds
        omega
      rw [PV_RunJoin_WeightPowersThread47.more x p out i hi hm,
        AspisR1ProducerRelease47.power_fill]
      simp only [if_neg hzero,if_neg hone,Array.index_mut_usize,hread,bind_tc_ok,
        PV_RunJoin_WeightWide46.mul_value,lift]
      rw [←PV_RunJoin_WeightBorrow46.restore]
      exact ih _ _ _ _ hd (by rw [hv];omega)
#print axioms complete
end R1Z.PV_RunJoin_WeightPowersLoop47
