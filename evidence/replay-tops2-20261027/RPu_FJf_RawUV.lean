import RPu_FJf_RawFoldBound
set_option autoImplicit false
namespace AspisR1.FJf_RawUV
open Aeneas Aeneas.Std
open FJf_RawReference
open FJf_RawArithmetic

theorem u_value (c d g h : U32)
    (hc : c.val < 2147483647) (hd : d.val < 2147483647)
    (hg : g.val < 2147483647) (hh : h.val < 2147483647) :
    (u c d g h).val=JFv_TX2_FoldValue.value (c.val*g.val+4611686014132420609-d.val*h.val) ∧
    (u c d g h).val≤6442450941 := by
  have bc := product_bound c g hc hg
  have bd := product_bound d h hd hh
  have va : (add (product c g) 4611686014132420609#u64).val=
      (product c g).val+4611686014132420609 := by
    apply add_value
    rw [product_value]
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits]
    omega
  have vs : (sub (add (product c g) 4611686014132420609#u64) (product d h)).val=
      c.val*g.val+4611686014132420609-d.val*h.val := by
    rw [sub_value,va,product_value,product_value]
    rw [va,product_value,product_value]
    omega
  have small : (sub (add (product c g) 4611686014132420609#u64) (product d h)).val≤9223372028264841218 := by
    rw [vs];omega
  constructor
  · unfold u
    rw [JFv_TX2_FoldValue.source,vs]
  · exact FJf_RawFoldBound.typed _ small

theorem v_value (c d g h : U32)
    (hc : c.val < 2147483647) (hd : d.val < 2147483647)
    (hg : g.val < 2147483647) (hh : h.val < 2147483647) :
    (v c d g h).val=JFv_TX2_FoldValue.value (c.val*h.val+d.val*g.val) ∧
    (v c d g h).val≤6442450941 := by
  have bc := product_bound c h hc hh
  have bd := product_bound d g hd hg
  have va : (add (product c h) (product d g)).val=c.val*h.val+d.val*g.val := by
    rw [add_value,product_value,product_value]
    rw [product_value,product_value]
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits]
    omega
  have small : (add (product c h) (product d g)).val≤9223372028264841218 := by rw [va];omega
  constructor
  · unfold v
    rw [JFv_TX2_FoldValue.source,va]
  · exact FJf_RawFoldBound.typed _ small
#print axioms u_value
#print axioms v_value
end AspisR1.FJf_RawUV
