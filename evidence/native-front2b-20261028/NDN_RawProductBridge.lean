import NDN_Reference6.Funs
import NDN_Reference8.Funs
import NDE_StubWordBounds
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDN_RawProductBridge

theorem product (a b : U32) (ha:a.val<2147483647) (hb:b.val<2147483647) :
 ∃ z, (core.convert.num.FromU64U32.from a * core.convert.num.FromU64U32.from b)=ok z ∧
 z.val=a.val*b.val := by
 let x := core.convert.num.FromU64U32.from a
 let y := core.convert.num.FromU64U32.from b
 have hx : x.val=a.val := by
  change (BitVec.setWidth 64 a.bv).toNat=a.val
  rw [BitVec.toNat_setWidth]
  change a.val % 2^64=a.val
  exact Nat.mod_eq_of_lt (by scalar_tac)
 have hy : y.val=b.val := by
  change (BitVec.setWidth 64 b.bv).toNat=b.val
  rw [BitVec.toNat_setWidth]
  change b.val % 2^64=b.val
  exact Nat.mod_eq_of_lt (by scalar_tac)
 have hp := NDE_StubWordBounds.product a.val b.val ha hb
 obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=x) (y:=y) (by scalar_tac))
 refine ⟨z,hz,?_⟩
 simpa only [hx,hy] using hv

theorem accumulation (raw product : U64) (h:raw.val+product.val<2^64) :
 ∃ z,NDN_Reference6.add_product raw product=ok z ∧ z.val=raw.val+product.val := by
 obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=raw) (y:=product) (by scalar_tac))
 exact ⟨z,hz,hv⟩

theorem next_index (i : Usize) (hi:i.val<272) :
 ∃ j,NDN_Reference8.next_index i=ok j ∧ j.val=i.val+1 := by
 obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
 exact ⟨z,hz,hv⟩

#print axioms product
#print axioms accumulation
#print axioms next_index
end NDN_RawProductBridge
