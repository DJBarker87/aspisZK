import AspisV8R19.ProductExecution

/-! The source product's natural-number coordinates are the exact field
product. No canonical-product or no-failure premise is assumed. -/
set_option autoImplicit false
namespace AspisV8R19.ProductCorrectness
open Aeneas Aeneas.Std Result AspisR69Explicit ProductExecution
open AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase encodeBase_val encodeBase_cast eq_encodeBase)
noncomputable section

theorem raw_coordinates (a b c d e f g h : M31Exact) :
    rawOutput a.val b.val c.val d.val e.val f.val g.val h.val =
      encode ((⟨⟨a,b⟩,⟨c,d⟩⟩ : QM31Exact) * ⟨⟨e,f⟩,⟨g,h⟩⟩) := by
  have prod (x y : M31Exact) : x.val*y.val < PartialProduct.p*PartialProduct.p :=
    PartialProduct.product_bound _ _ (ZMod.val_lt x) (ZMod.val_lt y)
  have hi := PartialProduct.intermediate_bounds _ _ _ _ (prod c g) (prod d h) (prod c h) (prod d g)
  have hu : rawU c.val d.val g.val h.val < 3*P := PartialProduct.partial_bound _ hi.2.2.1
  have hv : rawV c.val d.val g.val h.val < 3*P := PartialProduct.partial_bound _ hi.2.2.2
  have hfirst := PartialProduct.reconstruction_bounds _ _ _ _
    (rawU c.val d.val g.val h.val) (rawV c.val d.val g.val h.val)
    (prod a e) (prod b f) (prod a f) (prod b e) hu hv
  have hthird := PartialDot.third_coordinate_bounds _ _ _ _ (prod a g) (prod c e) (prod b h) (prod d f)
  simp only [PartialProduct.p] at hi hfirst hthird
  have foldcast (n : Nat) : (PartialProduct.foldOnce n : M31Exact) = (n : M31Exact) := by
    have hm : PartialProduct.foldOnce n % P = n % P := PartialProduct.partial_mod n
    have he := congrArg (fun k : Nat => (k : M31Exact)) hm
    simpa only [ZMod.natCast_mod] using he
  have pzero : (2147483647 : M31Exact) = 0 := by
    exact ZMod.natCast_self P
  have ucast : (rawU c.val d.val g.val h.val : M31Exact) = c*g-d*h := by
    unfold rawU
    rw [foldcast,Nat.cast_sub hi.1]
    simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val,ZMod.natCast_self,mul_zero,add_zero]
  have vcast : (rawV c.val d.val g.val h.val : M31Exact) = c*h+d*g := by
    unfold rawV
    rw [foldcast]
    simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val]
  have c0 : (raw0 a.val b.val c.val d.val e.val f.val g.val h.val : M31Exact) =
      a*e-b*f+2*(c*g-d*h)-(c*h+d*g) := by
    unfold raw0
    rw [Nat.cast_sub hfirst.2.2.1]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hfirst.1,Nat.cast_ofNat,
      ZMod.natCast_zmod_val,ucast,vcast,pzero,mul_zero,add_zero]
  have c1 : (raw1 a.val b.val c.val d.val e.val f.val g.val h.val : M31Exact) =
      a*f+b*e+(c*g-d*h)+2*(c*h+d*g) := by
    simp only [raw1,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val,ucast,vcast]
  have c2 : (raw2 a.val b.val c.val d.val e.val f.val g.val h.val : M31Exact) =
      a*g+c*e-b*h-d*f := by
    simp only [raw2,← Nat.mul_assoc,P]
    rw [Nat.cast_sub hthird.2.2,Nat.cast_sub hthird.2.1]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val,
      pzero,mul_zero,add_zero]
  have c3 : (raw3 a.val b.val c.val d.val e.val f.val g.val h.val : M31Exact) =
      a*h+b*g+c*f+d*e := by
    simp only [raw3,Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val]
  have he : (⟨⟨a*e-b*f+2*(c*g-d*h)-(c*h+d*g),a*f+b*e+(c*g-d*h)+2*(c*h+d*g)⟩,
                ⟨a*g+c*e-b*h-d*f,a*h+b*g+c*f+d*e⟩⟩ : QM31Exact) =
      (⟨⟨a,b⟩,⟨c,d⟩⟩ : QM31Exact)*⟨⟨e,f⟩,⟨g,h⟩⟩ := by
    apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
      simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
        QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,
        qm31R_re,qm31R_im,QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero] <;> ring
  rw [← he]
  simp only [rawOutput,encode,encodeCM,c0,c1,c2,c3]

theorem canonical_product (x y : QM31Exact) :
    field.r24_canonical_mul (encode x) (encode y) = .ok (some (encode (x*y))) := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rcases y with ⟨⟨e,f⟩,⟨g,h⟩⟩
  rw [product_raw,raw_coordinates]

theorem public_product (x y : QM31Exact) :
    field.QM31.mul (encode x) (encode y) = .ok (encode (x*y)) := by
  simp only [field.QM31.mul,canonical_product,bind_tc_ok]

def decode (x : field.QM31) : QM31Exact :=
  ⟨⟨(x.c0.a.val : M31Exact),(x.c0.b.val : M31Exact)⟩,
   ⟨(x.c1.a.val : M31Exact),(x.c1.b.val : M31Exact)⟩⟩
def Canonical (x : field.QM31) : Prop :=
  x.c0.a.val < P ∧ x.c0.b.val < P ∧ x.c1.a.val < P ∧ x.c1.b.val < P

theorem encode_canonical (x : QM31Exact) : Canonical (encode x) :=
  ⟨ZMod.val_lt x.re.re,ZMod.val_lt x.re.im,ZMod.val_lt x.im.re,ZMod.val_lt x.im.im⟩

theorem decode_encode (x : QM31Exact) : decode (encode x) = x := by
  apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
    simp only [decode,encode,encodeCM,encodeBase_cast]

theorem encode_decode (x : field.QM31) (hc : Canonical x) : encode (decode x) = x := by
  have ha := eq_encodeBase x.c0.a (x.c0.a.val : M31Exact) hc.1 rfl
  have hb := eq_encodeBase x.c0.b (x.c0.b.val : M31Exact) hc.2.1 rfl
  have hc' := eq_encodeBase x.c1.a (x.c1.a.val : M31Exact) hc.2.2.1 rfl
  have hd := eq_encodeBase x.c1.b (x.c1.b.val : M31Exact) hc.2.2.2 rfl
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp only [encode,decode,encodeCM,← ha,← hb,← hc',← hd]

theorem guard_execution (x y : field.QM31) (hx : Canonical x) (hy : Canonical y) :
    field.r24_canonical_mul x y = .ok (some (encode (decode x * decode y))) := by
  conv_lhs => rw [← encode_decode x hx,← encode_decode y hy]
  exact canonical_product (decode x) (decode y)

theorem public_execution (x y : field.QM31) (hx : Canonical x) (hy : Canonical y) :
    field.QM31.mul x y = .ok (encode (decode x * decode y)) := by
  conv_lhs => rw [← encode_decode x hx,← encode_decode y hy]
  exact public_product (decode x) (decode y)

theorem result_correct (x y : field.QM31) (hx : Canonical x) (hy : Canonical y) :
    ∃ z, field.QM31.mul x y = .ok z ∧ Canonical z ∧ decode z = decode x * decode y :=
  ⟨encode (decode x * decode y),public_execution x y hx hy,encode_canonical _,decode_encode _⟩

theorem no_failure (x y : field.QM31) (hx : Canonical x) (hy : Canonical y) (e : Error) :
    field.QM31.mul x y ≠ .fail e := by rw [public_execution x y hx hy]; simp

#print axioms raw_coordinates
#print axioms canonical_product
#print axioms public_product
#print axioms encode_canonical
#print axioms decode_encode
#print axioms encode_decode
#print axioms guard_execution
#print axioms public_execution
#print axioms result_correct
#print axioms no_failure
end
end AspisV8R19.ProductCorrectness
