import CuSavingsLibraSourceFactored
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraSourcePrepare
open Aeneas Aeneas.Std Result AspisR1Libra
open CuSavingsLibraSourceModel CuSavingsLibraSourceControl CuSavingsLibraSourceFactored
variable {R S : Type} [CommSemiring R] [CommSemiring S] [Shared]
variable (A : Arithmetic R S)

def point (p : Points) (i : Nat) : R :=
  A.decodeE (lookup p field.wide_exact.WideExact.ZERO (CuSavingsLibraSourcePerm.perm i))
def lowValue (p : Points) (q : K) : R :=
  CuSavingsLibra.lowRun (point A p) A.quarter (A.embedding (A.decodeK q))
def highTerm (p : Points) (q : K) (i : Nat) : R :=
  point A p i*A.quarter*(A.embedding (A.decodeK q))^(4*i)

structure Valid (ap0 ap1 : Points) (q : K) (data : Prepared) : Prop where
  lowC : A.canonicalE data.low
  first2C : A.canonicalE data.first2
  first3C : A.canonicalE data.first3
  allC : A.canonicalE data.all
  q4C : A.canonicalK data.q4
  q16C : A.canonicalK data.q16
  lowV : A.decodeE data.low=lowValue A ap0 q
  first2V : A.decodeE data.first2=highTerm A ap1 q 0+highTerm A ap1 q 1
  first3V : A.decodeE data.first3=highTerm A ap1 q 0+highTerm A ap1 q 1+highTerm A ap1 q 2
  allV : A.decodeE data.all=highTerm A ap1 q 0+highTerm A ap1 q 1+highTerm A ap1 q 2+highTerm A ap1 q 3
  q4V : A.decodeK data.q4=(A.decodeK q)^4
  q16V : A.decodeK data.q16=(A.decodeK q)^16

theorem source_success (ap0 ap1 : Points) (q : K)
    (hp0 : ∀ i, i<4 → A.canonicalE (lookup ap0 field.wide_exact.WideExact.ZERO i))
    (hp1 : ∀ i, i<4 → A.canonicalE (lookup ap1 field.wide_exact.WideExact.ZERO i))
    (hq : A.canonicalK q) :
    ∃ data, prepare ap0 ap1 q=.ok data ∧ Valid A ap0 ap1 q data := by
  obtain ⟨powers,hpowers,hpv⟩ := CuSavingsLibraSourcePowers.source_success A 4#usize q hq (by scalar_tac)
  have powerValues (i : Nat) (hi : i<4) :
      A.canonicalK (lookup powers field.QM31.ONE i) ∧
        A.decodeK (lookup powers field.QM31.ONE i)=(A.decodeK q)^i := by
    have hiv : i<(4#usize).val := by scalar_tac
    have hlen : i<powers.val.length := by rw [powers.property];exact hiv
    simpa only [lookup,List.getD_eq_getElem powers.val field.QM31.ONE hlen] using hpv i hiv
  let q2 := lookup powers field.QM31.ONE 2
  have hr2 := read powers field.QM31.ONE 2#usize (by scalar_tac)
  obtain ⟨q4,hq4,hq4C,hq4V⟩ := A.square q2 (powerValues 2 (by omega)).1
  have vq4 : A.decodeK q4=(A.decodeK q)^4 := by
    rw [hq4V,(powerValues 2 (by omega)).2,←pow_mul]
  obtain ⟨q8,hq8,hq8C,hq8V⟩ := A.square q4 hq4C
  have vq8 : A.decodeK q8=(A.decodeK q)^8 := by rw [hq8V,vq4,←pow_mul]
  obtain ⟨q12,hq12,hq12C,hq12V⟩ := A.kmul q8 q4 hq8C hq4C
  have vq12 : A.decodeK q12=(A.decodeK q)^12 := by rw [hq12V,vq8,vq4,←pow_add]
  obtain ⟨q16,hq16,hq16C,hq16V⟩ := A.square q8 hq8C
  have vq16 : A.decodeK q16=(A.decodeK q)^16 := by rw [hq16V,vq8,←pow_mul]
  obtain ⟨low,hlow,hlowC,hlowV⟩ := CuSavingsLibraSourceScalar.source_success A powers ap0
    (fun i hi => (powerValues i hi).1) hp0
  have lowV : A.decodeE low=lowValue A ap0 q := by
    rw [hlowV]
    unfold CuSavingsLibraSourceScalar.partialSum lowValue CuSavingsLibra.lowRun
    calc
      _ = ((List.range 4).map (fun i => CuSavingsLibraSourceScalar.term A powers ap0 i*A.quarter)).sum :=
        (List.sum_map_mul_right _ _ _).symm
      _ = _ := by
        congr 1
        apply List.map_congr_left
        intro i hi
        unfold CuSavingsLibraSourceScalar.term point
        rw [(powerValues i (List.mem_range.mp hi)).2,map_pow]
        ring
  let high : Powers := Array.make 4#usize [field.QM31.ONE,q4,q8,q12]
  have highValues (i : Nat) (hi : i<4) : A.canonicalK (lookup high field.QM31.ONE i) ∧
      A.decodeK (lookup high field.QM31.ONE i)=(A.decodeK q)^(4*i) := by
    have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    · simpa [high,lookup,Array.make] using And.intro A.one A.one_value
    · simpa [high,lookup,Array.make] using And.intro hq4C vq4
    · simpa [high,lookup,Array.make] using And.intro hq8C vq8
    · simpa [high,lookup,Array.make] using And.intro hq12C vq12
  obtain ⟨terms,hterms,htv⟩ := CuSavingsLibraSourceTerms.source_success A ap1 high hp1
    (fun i hi => (highValues i hi).1)
  have termValues (i : Nat) (hi : i<4) :
      A.canonicalE (lookup terms field.wide_exact.WideExact.ZERO i) ∧
      A.decodeE (lookup terms field.wide_exact.WideExact.ZERO i)=highTerm A ap1 q i := by
    refine ⟨(htv i hi).1,?_⟩
    rw [(htv i hi).2]
    unfold CuSavingsLibraSourceTerms.term highTerm point
    rw [(highValues i hi).2,map_pow]
    ring
  let t0 := lookup terms field.wide_exact.WideExact.ZERO 0
  let t1 := lookup terms field.wide_exact.WideExact.ZERO 1
  let t2 := lookup terms field.wide_exact.WideExact.ZERO 2
  let t3 := lookup terms field.wide_exact.WideExact.ZERO 3
  obtain ⟨first2,hfirst2,hfirst2C,hfirst2V⟩ := A.add t0 t1
    (termValues 0 (by omega)).1 (termValues 1 (by omega)).1
  obtain ⟨first3,hfirst3,hfirst3C,hfirst3V⟩ := A.add first2 t2 hfirst2C (termValues 2 (by omega)).1
  obtain ⟨all,hall,hallC,hallV⟩ := A.add first3 t3 hfirst3C (termValues 3 (by omega)).1
  let data : Prepared := ⟨low,first2,first3,all,q4,q16⟩
  refine ⟨data,?_,hlowC,hfirst2C,hfirst3C,hallC,hq4C,hq16C,lowV,?_,?_,?_,vq4,vq16⟩
  · have hrt (i : Usize) (hi : i.val<4) := read terms field.wide_exact.WideExact.ZERO i (by scalar_tac)
    unfold prepare
    simp only [hpowers,hr2,hq4,hq8,hq12,hq16,hlow,hterms,
      hrt 0#usize (by scalar_tac),hrt 1#usize (by scalar_tac),hrt 2#usize (by scalar_tac),hrt 3#usize (by scalar_tac),
      hfirst2,hfirst3,hall,bind_tc_ok]
    rfl
  · simpa only [(termValues 0 (by omega)).2,(termValues 1 (by omega)).2] using hfirst2V
  · rw [hfirst3V,hfirst2V,(termValues 0 (by omega)).2,(termValues 1 (by omega)).2,(termValues 2 (by omega)).2]
  · rw [hallV,hfirst3V,hfirst2V,(termValues 0 (by omega)).2,(termValues 1 (by omega)).2,
      (termValues 2 (by omega)).2,(termValues 3 (by omega)).2]

#print axioms source_success
end AspisR1.CuSavingsLibraSourcePrepare
