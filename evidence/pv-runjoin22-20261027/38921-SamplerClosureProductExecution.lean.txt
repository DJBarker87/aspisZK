/- Mechanically reused R70/R71 proof script for the actual R72 closure.
Only identifier renaming and removal of the absent diagnostic-probe corollary.
Checked by tools/generate_r78_closure.py; original files are preserved. -/
import AspisV8R19.SamplerClosureExplicitWord

/-! Symbolic execution of the full extracted canonical product. This leaf
returns its exact natural-number coordinates; the next bridge identifies
those residues with multiplication in the retained QM31 field tower. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerClosureProductExecution
open Aeneas Aeneas.Std Result AspisR72Sampler SamplerClosureExplicitWord
open AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase encodeBase_val)
noncomputable section

def encodeCM (x : CM31Exact) : field.CM31 := ⟨encodeBase x.re,encodeBase x.im⟩
def encode (x : QM31Exact) : field.QM31 := ⟨encodeCM x.re,encodeCM x.im⟩
def rawU (c d g h : Nat) := PartialProduct.foldOnce (c*g+P*P-d*h)
def rawV (c d g h : Nat) := PartialProduct.foldOnce (c*h+d*g)
def raw0 (a b c d e f g h : Nat) :=
  a*e+P*P-b*f+2*rawU c d g h+3*P-rawV c d g h
def raw1 (a b c d e f g h : Nat) :=
  a*f+b*e+rawU c d g h+2*rawV c d g h
def raw2 (a b c d e f g h : Nat) := a*g+c*e+2*(P*P)-b*h-d*f
def raw3 (a b c d e f g h : Nat) := a*h+b*g+c*f+d*e
def rawOutput (a b c d e f g h : Nat) : field.QM31 :=
  ⟨⟨encodeBase (raw0 a b c d e f g h : M31Exact),
     encodeBase (raw1 a b c d e f g h : M31Exact)⟩,
   ⟨encodeBase (raw2 a b c d e f g h : M31Exact),
     encodeBase (raw3 a b c d e f g h : M31Exact)⟩⟩

theorem encoded_guard (x : M31Exact) : ¬ field.P ≤ encodeBase x := by
  rw [UScalar.le_equiv,encodeBase_val]
  have hp : field.P.val = P := by simp [field.P,P]
  rw [hp]
  exact Nat.not_le.mpr (ZMod.val_lt x)

theorem product_raw (x y : QM31Exact) :
    field.r24_canonical_mul (encode x) (encode y) =
      .ok (some (rawOutput x.re.re.val x.re.im.val x.im.re.val x.im.im.val
        y.re.re.val y.re.im.val y.im.re.val y.im.im.val)) := by
  let a := x.re.re.val
  have ha : a < PartialProduct.p := ZMod.val_lt x.re.re
  let b := x.re.im.val
  have hb : b < PartialProduct.p := ZMod.val_lt x.re.im
  let c := x.im.re.val
  have hc : c < PartialProduct.p := ZMod.val_lt x.im.re
  let d := x.im.im.val
  have hd : d < PartialProduct.p := ZMod.val_lt x.im.im
  let e := y.re.re.val
  have he : e < PartialProduct.p := ZMod.val_lt y.re.re
  let f := y.re.im.val
  have hf : f < PartialProduct.p := ZMod.val_lt y.re.im
  let g := y.im.re.val
  have hg : g < PartialProduct.p := ZMod.val_lt y.im.re
  let h := y.im.im.val
  have hh : h < PartialProduct.p := ZMod.val_lt y.im.im
  have hae := PartialProduct.product_bound a e ha he
  have haf := PartialProduct.product_bound a f ha hf
  have hag := PartialProduct.product_bound a g ha hg
  have hah := PartialProduct.product_bound a h ha hh
  have hbe := PartialProduct.product_bound b e hb he
  have hbf := PartialProduct.product_bound b f hb hf
  have hbg := PartialProduct.product_bound b g hb hg
  have hbh := PartialProduct.product_bound b h hb hh
  have hce := PartialProduct.product_bound c e hc he
  have hcf := PartialProduct.product_bound c f hc hf
  have hcg := PartialProduct.product_bound c g hc hg
  have hch := PartialProduct.product_bound c h hc hh
  have hde := PartialProduct.product_bound d e hd he
  have hdf := PartialProduct.product_bound d f hd hf
  have hdg := PartialProduct.product_bound d g hd hg
  have hdh := PartialProduct.product_bound d h hd hh
  have hi := PartialProduct.intermediate_bounds (c*g) (d*h) (c*h) (d*g) hcg hdh hch hdg
  have hu : rawU c d g h < 3*P := PartialProduct.partial_bound _ hi.2.2.1
  have hv : rawV c d g h < 3*P := PartialProduct.partial_bound _ hi.2.2.2
  have hfirst := PartialProduct.reconstruction_bounds (a*e) (b*f) (a*f) (b*e)
    (rawU c d g h) (rawV c d g h) hae hbf haf hbe hu hv
  have hthird := PartialDot.third_coordinate_bounds (a*g) (c*e) (b*h) (d*f) hag hce hbh hdf
  have hfourth := PartialDot.fourth_coordinate_bound (a*h) (b*g) (c*f) (d*e) hah hbg hcf hde
  simp only [field.r24_canonical_mul,encode,encodeCM,encoded_guard,if_false,lift,bind_tc_ok,widen_encode]
  change _ = Result.ok (some (rawOutput a b c d e f g h))
  simp only [rawOutput,raw0,raw1,raw2,raw3]
  dsimp only [a,b,c,d,e,f,g,h,rawU,rawV] at *
  simp (disch := (simp only [P,PartialProduct.p] at *; omega)) only
    [pp_word,prime_from,two_word,three_word,word_mul,word_add,word_sub,
     partial_word,reduce_word,field.CM31.new,bind_tc_ok]

#print axioms encoded_guard
#print axioms product_raw
end
end AspisV8R19.SamplerClosureProductExecution
