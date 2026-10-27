import FIo_GroupSubset
set_option autoImplicit false
namespace AspisR1.FJc_MaskBits
open Aeneas Aeneas.Std Result WP
/-- Actual u16 shift used by the inactive subset is an exact power of two. -/
theorem shift (bit : Usize) (out : U16) (hb : bit.val<16)
    (run : (1#u16 <<< bit : Result U16)=ok out) : out.val=2^bit.val := by
  obtain ⟨x,hx,hv,_⟩ := WP.spec_imp_exists (U16.ShiftLeft_spec 1#u16 bit hb)
  have eq := Result.ok.inj (hx.symm.trans run)
  subst x
  rw [Nat.shiftLeft_eq] at hv
  have bound : 2^bit.val<2^16 := Nat.pow_lt_pow_right (by decide) hb
  rw [U16.size,U16.numBits,show (1#u16).val=1 from by decide] at hv
  simpa only [UScalarTy.numBits,one_mul,Nat.mod_eq_of_lt bound] using hv

theorem selected (mask shifted : U16) (bit : Usize) (hb : bit.val<16)
    (run : (1#u16 <<< bit : Result U16)=ok shifted) :
    (mask &&& shifted) ≠ 0#u16 ↔ (mask.val &&& 2^bit.val)≠0 := by
  constructor
  · intro h hz
    apply h
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and,shift bit shifted hb run,hz]
    rfl
  · intro h hz
    apply h
    have hv := congrArg UScalar.val hz
    simpa only [UScalar.val_and,shift bit shifted hb run,show (0#u16).val=0 from by decide] using hv
#print axioms shift
#print axioms selected
end AspisR1.FJc_MaskBits
