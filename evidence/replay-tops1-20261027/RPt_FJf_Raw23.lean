import RPt_FJf_RawUV
set_option autoImplicit false
namespace AspisR1.FJf_Raw23
open Aeneas Aeneas.Std
open FJf_RawReference FJf_RawArithmetic

theorem lane2 (a b c d e f g h : U32)
    (ha : a.val < 2147483647) (hb : b.val < 2147483647)
    (hc : c.val < 2147483647) (hd : d.val < 2147483647)
    (he : e.val < 2147483647) (hf : f.val < 2147483647)
    (hg : g.val < 2147483647) (hh : h.val < 2147483647) :
    (raw2 a b c d e f g h).val=
      a.val*g.val+c.val*e.val+9223372028264841218-b.val*h.val-d.val*f.val := by
  have bag := product_bound a g ha hg
  have bce := product_bound c e hc he
  have bbh := product_bound b h hb hh
  have bdf := product_bound d f hd hf
  let t1 := add (product a g) (product c e)
  have v1 : t1.val=a.val*g.val+c.val*e.val := by
    rw [add_value,product_value,product_value]
    rw [product_value,product_value]
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits];omega
  let t2 := add t1 9223372028264841218#u64
  have v2 : t2.val=a.val*g.val+c.val*e.val+9223372028264841218 := by
    rw [add_value,v1,show (9223372028264841218#u64).val=9223372028264841218 from by decide]
    rw [v1]
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits];omega
  have v3 := sub_value t2 (product b h) (by rw [v2,product_value];omega)
  have v4 := sub_value (sub t2 (product b h)) (product d f)
    (by rw [v3,v2,product_value,product_value];omega)
  change (sub (sub t2 (product b h)) (product d f)).val=_
  rw [v4,v3,v2,product_value,product_value]

theorem lane3 (a b c d e f g h : U32)
    (ha : a.val < 2147483647) (hb : b.val < 2147483647)
    (hc : c.val < 2147483647) (hd : d.val < 2147483647)
    (he : e.val < 2147483647) (hf : f.val < 2147483647)
    (hg : g.val < 2147483647) (hh : h.val < 2147483647) :
    (raw3 a b c d e f g h).val=a.val*h.val+b.val*g.val+c.val*f.val+d.val*e.val := by
  have bah := product_bound a h ha hh
  have bbg := product_bound b g hb hg
  have bcf := product_bound c f hc hf
  have bde := product_bound d e hd he
  let t1 := add (product a h) (product b g)
  have v1 : t1.val=a.val*h.val+b.val*g.val := by
    rw [add_value,product_value,product_value]
    rw [product_value,product_value]
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits];omega
  let t2 := add t1 (product c f)
  have v2 : t2.val=a.val*h.val+b.val*g.val+c.val*f.val := by
    rw [add_value,v1,product_value]
    rw [v1,product_value]
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits];omega
  change (add t2 (product d e)).val=_
  rw [add_value,v2,product_value]
  rw [v2,product_value]
  norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits];omega
#print axioms lane2
#print axioms lane3
end AspisR1.FJf_Raw23
