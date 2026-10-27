import RPt_FJf_Raw23
set_option autoImplicit false
namespace AspisR1.FJf_Raw01
open Aeneas Aeneas.Std
open FJf_RawReference FJf_RawArithmetic

theorem lane0 (a b c d e f g h : U32)
    (ha : a.val < 2147483647) (hb : b.val < 2147483647)
    (hc : c.val < 2147483647) (hd : d.val < 2147483647)
    (he : e.val < 2147483647) (hf : f.val < 2147483647)
    (hg : g.val < 2147483647) (hh : h.val < 2147483647) :
    (raw0 a b c d e f g h).val=
      a.val*e.val+4611686014132420609-b.val*f.val+2*(u c d g h).val+
        6442450941-(v c d g h).val := by
  have bae := product_bound a e ha he
  have bbf := product_bound b f hb hf
  have bu := (FJf_RawUV.u_value c d g h hc hd hg hh).2
  have bv := (FJf_RawUV.v_value c d g h hc hd hg hh).2
  let t1 := add (product a e) 4611686014132420609#u64
  have v1 : t1.val=a.val*e.val+4611686014132420609 := by
    rw [add_value,product_value,show (4611686014132420609#u64).val=4611686014132420609 from by decide]
    rw [product_value]
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits];omega
  let t2 := sub t1 (product b f)
  have v2 : t2.val=a.val*e.val+4611686014132420609-b.val*f.val := by
    rw [sub_value,v1,product_value]
    rw [v1,product_value];omega
  let du := mul 2#u64 (u c d g h)
  have vu : du.val=2*(u c d g h).val := by
    apply mul_value
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits];omega
  let t3 := add t2 du
  have v3 : t3.val=t2.val+2*(u c d g h).val := by
    rw [add_value,vu]
    rw [v2,vu]
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits];omega
  let t4 := add t3 6442450941#u64
  have v4 : t4.val=t3.val+6442450941 := by
    apply add_value
    rw [v3,v2]
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits];omega
  change (sub t4 (v c d g h)).val=_
  rw [sub_value,v4,v3,v2]
  rw [v4];omega

theorem lane1 (a b c d e f g h : U32)
    (ha : a.val < 2147483647) (hb : b.val < 2147483647)
    (hc : c.val < 2147483647) (hd : d.val < 2147483647)
    (he : e.val < 2147483647) (hf : f.val < 2147483647)
    (hg : g.val < 2147483647) (hh : h.val < 2147483647) :
    (raw1 a b c d e f g h).val=
      a.val*f.val+b.val*e.val+(u c d g h).val+2*(v c d g h).val := by
  have baf := product_bound a f ha hf
  have bbe := product_bound b e hb he
  have bu := (FJf_RawUV.u_value c d g h hc hd hg hh).2
  have bv := (FJf_RawUV.v_value c d g h hc hd hg hh).2
  let t1 := add (product a f) (product b e)
  have v1 : t1.val=a.val*f.val+b.val*e.val := by
    rw [add_value,product_value,product_value]
    rw [product_value,product_value]
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits];omega
  let t2 := add t1 (u c d g h)
  have v2 : t2.val=t1.val+(u c d g h).val := by
    apply add_value
    rw [v1]
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits];omega
  let dv := mul 2#u64 (v c d g h)
  have vv : dv.val=2*(v c d g h).val := by
    apply mul_value
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits];omega
  change (add t2 dv).val=_
  rw [add_value,v2,v1,vv]
  rw [v2,v1,vv]
  norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits];omega
#print axioms lane0
#print axioms lane1
end AspisR1.FJf_Raw01
