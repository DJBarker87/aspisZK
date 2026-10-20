import CuSavingsLibraSourceArrays
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraSourceSides
open Aeneas Aeneas.Std Result AspisR1Libra
open CuSavingsLibraSourceModel CuSavingsLibraSourceControl CuSavingsLibraSourceFactored
open CuSavingsLibraSourcePrepare CuSavingsLibraSourceArrays
variable {R S : Type} [CommSemiring R] [CommSemiring S] [Shared]
variable (A : Arithmetic R S)

def first (ap0 ap1 : Points) (q : K) (previous : Nat → R) (j : Nat) : R :=
  if j=1 then lowValue A ap0 q*(highTerm A ap1 q 0+highTerm A ap1 q 1+highTerm A ap1 q 2)*
    (A.embedding (A.decodeK q))^16
  else if j=0 then lowValue A ap0 q*(highTerm A ap1 q 0+highTerm A ap1 q 1+highTerm A ap1 q 2+highTerm A ap1 q 3)
  else previous j

def second (ap0 ap1 : Points) (q : K) (previous : Nat → R) (j : Nat) : R :=
  if j=3 then lowValue A ap0 q*(highTerm A ap1 q 0+highTerm A ap1 q 1)*(A.embedding (A.decodeK q))^20
  else if j=2 then lowValue A ap0 q*(highTerm A ap1 q 0+highTerm A ap1 q 1+highTerm A ap1 q 2+highTerm A ap1 q 3)*
    (A.embedding (A.decodeK q))^4
  else if j=1 then previous 1+lowValue A ap0 q*(point A ap1 3*A.quarter)
  else previous j

theorem side0_success (ap0 ap1 : Points) (q : K) (data : Prepared) (weights : Points)
    (hd : Valid A ap0 ap1 q data) (hw : Canonical A weights) :
    ∃ result, side0 data weights=.ok result ∧ Canonical A result ∧
      ∀ j, j<4 → decoded A result j=first A ap0 ap1 q (decoded A weights) j := by
  obtain ⟨value0,h0,c0,v0⟩ := A.mul data.low data.all hd.lowC hd.allC
  obtain ⟨product,hp,cp,vp⟩ := A.mul data.low data.first3 hd.lowC hd.first3C
  obtain ⟨value1,h1,c1,v1⟩ := A.mixed product data.q16 cp hd.q16C
  let result := (weights.set 0#usize value0).set 1#usize value1
  refine ⟨result,?_,?_,?_⟩
  · unfold side0
    simp only [h0,hp,h1,update weights 0#usize value0 (by scalar_tac),
      update (weights.set 0#usize value0) 1#usize value1 (by scalar_tac),bind_tc_ok]
    rfl
  · exact update_canonical A _ _ (by scalar_tac) _
      (update_canonical A weights 0#usize (by scalar_tac) value0 hw c0) c1
  · intro j _
    simp only [result,decoded_set A _ 1#usize (by scalar_tac),decoded_set A _ 0#usize (by scalar_tac),
      show (1#usize).val=1 by scalar_tac,show (0#usize).val=0 by scalar_tac]
    rw [v0,v1,vp,hd.lowV,hd.allV,hd.first3V,hd.q16V,map_pow]
    rfl

theorem side1_success (ap0 ap1 : Points) (q : K) (data : Prepared) (weights : Points)
    (hd : Valid A ap0 ap1 q data) (hw : Canonical A weights)
    (hap1 : ∀ j, j<4 → A.canonicalE (lookup ap1 field.wide_exact.WideExact.ZERO j)) :
    ∃ result, side1 ap1 data weights=.ok result ∧ Canonical A result ∧
      ∀ j, j<4 → decoded A result j=second A ap0 ap1 q (decoded A weights) j := by
  let previous := lookup weights field.wide_exact.WideExact.ZERO 1
  have hrw := read weights field.wide_exact.WideExact.ZERO 1#usize (by scalar_tac)
  obtain ⟨index,hindex,hib,hiv⟩ := CuSavingsLibraSourcePerm.source 3#usize (by scalar_tac)
  have hrp := read ap1 field.wide_exact.WideExact.ZERO index (by scalar_tac)
  obtain ⟨tail,htail,ctail,vtail⟩ := A.scalar
    (lookup ap1 field.wide_exact.WideExact.ZERO index.val) (hap1 index.val hib)
  obtain ⟨term1,ht1,ct1,vt1⟩ := A.mul data.low tail hd.lowC ctail
  obtain ⟨value1,h1,c1,v1⟩ := A.add previous term1 (hw 1 (by omega)) ct1
  let weights1 := weights.set 1#usize value1
  obtain ⟨product2,hp2,cp2,vp2⟩ := A.mul data.low data.all hd.lowC hd.allC
  obtain ⟨value2,h2,c2,v2⟩ := A.mixed product2 data.q4 cp2 hd.q4C
  let weights2 := weights1.set 2#usize value2
  obtain ⟨product3,hp3,cp3,vp3⟩ := A.mul data.low data.first2 hd.lowC hd.first2C
  obtain ⟨scalar,hs,cs,vs⟩ := A.kmul data.q16 data.q4 hd.q16C hd.q4C
  obtain ⟨value3,h3,c3,v3⟩ := A.mixed product3 scalar cp3 cs
  let result := weights2.set 3#usize value3
  refine ⟨result,?_,?_,?_⟩
  · dsimp only [previous] at h1
    have hu2 := update weights1 2#usize value2 (by scalar_tac)
    have hu3 := update weights2 3#usize value3 (by scalar_tac)
    dsimp only [weights1] at hu2
    dsimp only [weights1,weights2] at hu3
    unfold side1
    simp only [CuSavingsLibraSourceTerms.perm_eq,CuSavingsLibraSourceTerms.quarter_eq,
      show (1#usize).val=1 by scalar_tac,hrw,hindex,hrp,htail,ht1,h1,hp2,h2,hp3,hs,h3,
      update weights 1#usize value1 (by scalar_tac),hu2,hu3,bind_tc_ok]
    rfl
  · exact update_canonical A _ _ (by scalar_tac) _
      (update_canonical A _ _ (by scalar_tac) _
        (update_canonical A weights 1#usize (by scalar_tac) value1 hw c1) c2) c3
  · intro j _
    simp only [result,weights2,weights1,decoded_set A _ 3#usize (by scalar_tac),
      decoded_set A _ 2#usize (by scalar_tac),decoded_set A _ 1#usize (by scalar_tac),
      show (1#usize).val=1 by scalar_tac,show (2#usize).val=2 by scalar_tac,show (3#usize).val=3 by scalar_tac]
    rw [v3,v2,v1,vp3,vs,vp2,vt1,vtail,hiv,hd.lowV,hd.first2V,hd.allV,hd.q16V,hd.q4V,map_mul,map_pow,map_pow]
    have hpow : (A.embedding (A.decodeK q))^16*(A.embedding (A.decodeK q))^4=(A.embedding (A.decodeK q))^20 := by rw [←pow_add]
    rw [hpow]
    unfold second point decoded
    by_cases h : j=1
    · subst j
      simp only [show (3#usize).val=3 by scalar_tac,↓reduceIte,previous]
      rfl
    · simp only [h,↓reduceIte]
      rfl

#print axioms side0_success
#print axioms side1_success
end AspisR1.CuSavingsLibraSourceSides
