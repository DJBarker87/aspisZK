import FJf_RawResidue
set_option autoImplicit false
namespace AspisR1.FJf_RawField
open Aeneas Aeneas.Std
open FJf_RawReference FJf_RawArithmetic
open FJf_RawResidue (F)

theorem lane0 (a b c d e f g h : U32)
    (ha : a.val < 2147483647) (hb : b.val < 2147483647)
    (hc : c.val < 2147483647) (hd : d.val < 2147483647)
    (he : e.val < 2147483647) (hf : f.val < 2147483647)
    (hg : g.val < 2147483647) (hh : h.val < 2147483647) :
    ((raw0 a b c d e f g h).val : F)=
      (a.val:F)*e.val-(b.val:F)*f.val+2*((c.val:F)*g.val-(d.val:F)*h.val)-
        ((c.val:F)*h.val+(d.val:F)*g.val) := by
  have bbf := product_bound b f hb hf
  have bv := (FJf_RawUV.v_value c d g h hc hd hg hh).2
  have inner : b.val*f.val≤a.val*e.val+4611686014132420609 := by omega
  have outer : (v c d g h).val≤a.val*e.val+4611686014132420609-b.val*f.val+
      2*(u c d g h).val+6442450941 := by omega
  rw [FJf_Raw01.lane0 a b c d e f g h ha hb hc hd he hf hg hh,Nat.cast_sub outer,
    Nat.cast_add,Nat.cast_add,Nat.cast_sub inner]
  simp only [Nat.cast_add,Nat.cast_mul,FJf_RawResidue.pp,FJf_RawResidue.triple_p]
  rw [FJf_RawResidue.u_value c d g h hc hd hg hh,FJf_RawResidue.v_value c d g h hc hd hg hh]
  ring

theorem lane1 (a b c d e f g h : U32)
    (ha : a.val < 2147483647) (hb : b.val < 2147483647)
    (hc : c.val < 2147483647) (hd : d.val < 2147483647)
    (he : e.val < 2147483647) (hf : f.val < 2147483647)
    (hg : g.val < 2147483647) (hh : h.val < 2147483647) :
    ((raw1 a b c d e f g h).val : F)=
      (a.val:F)*f.val+(b.val:F)*e.val+((c.val:F)*g.val-(d.val:F)*h.val)+
        2*((c.val:F)*h.val+(d.val:F)*g.val) := by
  rw [FJf_Raw01.lane1 a b c d e f g h ha hb hc hd he hf hg hh]
  simp only [Nat.cast_add,Nat.cast_mul]
  rw [FJf_RawResidue.u_value c d g h hc hd hg hh,FJf_RawResidue.v_value c d g h hc hd hg hh]
  ring

theorem lane2 (a b c d e f g h : U32)
    (ha : a.val < 2147483647) (hb : b.val < 2147483647)
    (hc : c.val < 2147483647) (hd : d.val < 2147483647)
    (he : e.val < 2147483647) (hf : f.val < 2147483647)
    (hg : g.val < 2147483647) (hh : h.val < 2147483647) :
    ((raw2 a b c d e f g h).val : F)=
      (a.val:F)*g.val+(c.val:F)*e.val-(b.val:F)*h.val-(d.val:F)*f.val := by
  have bbh := product_bound b h hb hh
  have bdf := product_bound d f hd hf
  have inner : b.val*h.val≤a.val*g.val+c.val*e.val+9223372028264841218 := by omega
  have outer : d.val*f.val≤a.val*g.val+c.val*e.val+9223372028264841218-b.val*h.val := by omega
  rw [FJf_Raw23.lane2 a b c d e f g h ha hb hc hd he hf hg hh,
    Nat.cast_sub outer,Nat.cast_sub inner]
  simp only [Nat.cast_add,Nat.cast_mul,FJf_RawResidue.twice_pp]
  ring

theorem lane3 (a b c d e f g h : U32)
    (ha : a.val < 2147483647) (hb : b.val < 2147483647)
    (hc : c.val < 2147483647) (hd : d.val < 2147483647)
    (he : e.val < 2147483647) (hf : f.val < 2147483647)
    (hg : g.val < 2147483647) (hh : h.val < 2147483647) :
    ((raw3 a b c d e f g h).val : F)=
      (a.val:F)*h.val+(b.val:F)*g.val+(c.val:F)*f.val+(d.val:F)*e.val := by
  rw [FJf_Raw23.lane3 a b c d e f g h ha hb hc hd he hf hg hh]
  simp only [Nat.cast_add,Nat.cast_mul]
#print axioms lane0
#print axioms lane1
#print axioms lane2
#print axioms lane3
end AspisR1.FJf_RawField
