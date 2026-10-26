import FIw_SelectorIndices
set_option autoImplicit false
namespace AspisR1.FIy_FrontierBits
open Aeneas Aeneas.Std Result WP

theorem low (index : U64) : (index &&& 1#u64).val=index.val%2 := by
  rw [UScalar.val_and]
  change index.val &&& 1=index.val%2
  exact Nat.and_two_pow_sub_one_eq_mod index.val 1
#print axioms low
theorem shift (index : U64) (level : Usize) (out : U64) (hl : level.val<20)
    (success : index >>> level=ok out) : out.val=index.val >>> level.val := by
  obtain ⟨out',hr,hv⟩ := WP.spec_imp_exists (UScalar.ShiftRight_spec index level
    (by change level.val<64;omega))
  have eq := Result.ok.inj (hr.symm.trans success)
  subst out'
  have value := congrArg BitVec.toNat hv.2
  simpa only [BitVec.toNat_ushiftRight,UScalar.bv_toNat] using value
#print axioms shift
end AspisR1.FIy_FrontierBits
