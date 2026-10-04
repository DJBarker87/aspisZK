import AspisV8R19.R163ComplexExecution
import AspisV8R19.R162WrappedWord
import AspisV8R19.SamplerClosureProductCorrectness

/-! Selected canonical QM31 product, proved by symbolic release-word
execution. The retained raw-coordinate algebra is transported through an
explicit value representation map only after actual source execution is proved. -/
set_option autoImplicit false
namespace AspisV8R19.R164ProductExecution
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core
open AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase encodeBase_val)
open R162WrappedWord (word word_value wrapping_add_word wrapping_mul_word wrapping_sub_word
  core_wrapping_add_word core_wrapping_sub_word)
noncomputable section

def encode (x : QM31Exact) : field.QM31 := ⟨R163ComplexExecution.encode x.re,R163ComplexExecution.encode x.im⟩
def fromOldCM (x : AspisR72Sampler.field.CM31) : field.CM31 := ⟨x.a,x.b⟩
def fromOld (x : AspisR72Sampler.field.QM31) : field.QM31 := ⟨fromOldCM x.c0,fromOldCM x.c1⟩

theorem encode_same (x : QM31Exact) :
    fromOld (SamplerClosureProductExecution.encode x) = encode x := rfl

abbrev rawU := SamplerClosureProductExecution.rawU
abbrev rawV := SamplerClosureProductExecution.rawV
abbrev raw0 := SamplerClosureProductExecution.raw0
abbrev raw1 := SamplerClosureProductExecution.raw1
abbrev raw2 := SamplerClosureProductExecution.raw2
abbrev raw3 := SamplerClosureProductExecution.raw3
def rawOutput (a b c d e f g h : Nat) : field.QM31 :=
  fromOld (SamplerClosureProductExecution.rawOutput a b c d e f g h)

theorem widen_encode (x : M31Exact) :
    UScalar.cast .U64 (encodeBase x) = word x.val := by
  apply UScalar.eq_of_val_eq
  rw [InverseRuntimeMul.cast_widen_value,encodeBase_val,word_value]
  have hx := ZMod.val_lt x
  unfold P at hx
  omega

theorem prime_word : UScalar.cast .U64 field.P = word P := by simp only [field.P]; rfl
theorem prime_from : core.convert.num.FromU64U32.from field.P = word P := by simp only [field.P]; rfl
theorem two_word : (2#u64 : U64) = word 2 := rfl
theorem three_word : (3#u64 : U64) = word 3 := rfl

theorem pp_word : field.r24_canonical_mul.PP = .ok (word (P*P)) := by
  simp only [field.r24_canonical_mul.PP,lift,bind_tc_ok,prime_word]
  exact SamplerClosureExplicitWord.word_mul P P (by decide) (by decide) (by decide)

theorem reduce_word (n : Nat) (hn : n < 2^64) :
    field.M31.reduce_u64 (word n) = .ok (encodeBase (n : M31Exact)) := by
  rw [R161WrappedMulExecution.reduce_encode,word_value n hn]

theorem partial_execution (x : U64) :
    field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call () x =
      .ok (word (PartialProduct.foldOnce x.val)) := by
  have he : field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call () x =
      .ok (R161WrappedMulExecution.wrappedFold x) := by
    simp only [field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call,
      lift,bind_tc_ok,R161WrappedMulExecution.wrappedFold]
    rfl
  rw [he]
  congr 1
  apply UScalar.eq_of_val_eq
  have hb := PartialDot.word_fold_bound x.val x.bv.isLt
  rw [R161WrappedMulExecution.wrappedFold_val,word_value _ (by omega)]
  unfold AspisV8R17.RawReducer.foldBits
  exact PartialProduct.source_fold x.val

theorem partial_word (n : Nat) (hn : n < 2^64) :
    field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call () (word n) =
      .ok (word (PartialProduct.foldOnce n)) := by
  rw [partial_execution,word_value n hn]

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
  simp only [field.r24_canonical_mul,encode,R163ComplexExecution.encode,encoded_guard,if_false,lift,bind_tc_ok,widen_encode]
  change _ = Result.ok (some (rawOutput a b c d e f g h))
  simp only [rawOutput,SamplerClosureProductExecution.rawOutput,fromOld,fromOldCM,SamplerClosureProductExecution.raw0,SamplerClosureProductExecution.raw1,
    SamplerClosureProductExecution.raw2,SamplerClosureProductExecution.raw3]
  dsimp only [a,b,c,d,e,f,g,h,rawU,rawV,SamplerClosureProductExecution.rawU,
    SamplerClosureProductExecution.rawV] at *
  simp (disch := (simp only [P,PartialProduct.p] at *; omega)) only
    [pp_word,prime_from,two_word,three_word,wrapping_mul_word,core_wrapping_add_word,core_wrapping_sub_word,
     partial_word,reduce_word,field.CM31.new,bind_tc_ok]

theorem raw_coordinates (a b c d e f g h : M31Exact) :
    rawOutput a.val b.val c.val d.val e.val f.val g.val h.val =
      encode ((⟨⟨a,b⟩,⟨c,d⟩⟩ : QM31Exact) * ⟨⟨e,f⟩,⟨g,h⟩⟩) := by
  exact congrArg fromOld (SamplerClosureProductCorrectness.raw_coordinates a b c d e f g h)

theorem canonical_product (x y : QM31Exact) :
    field.r24_canonical_mul (encode x) (encode y) = .ok (some (encode (x*y))) := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rcases y with ⟨⟨e,f⟩,⟨g,h⟩⟩
  rw [product_raw,raw_coordinates]

theorem public_product (x y : QM31Exact) :
    field.QM31.mul (encode x) (encode y) = .ok (encode (x*y)) := by
  simp only [field.QM31.mul,canonical_product,bind_tc_ok]

#print axioms encode_same
#print axioms widen_encode
#print axioms prime_word
#print axioms prime_from
#print axioms two_word
#print axioms three_word
#print axioms pp_word
#print axioms reduce_word
#print axioms partial_execution
#print axioms partial_word
#print axioms encoded_guard
#print axioms product_raw
#print axioms raw_coordinates
#print axioms canonical_product
#print axioms public_product
end
end AspisV8R19.R164ProductExecution
