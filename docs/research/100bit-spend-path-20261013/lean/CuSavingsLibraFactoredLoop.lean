import CuSavingsLibraSourceSides
import OccupancyRangeTraversal
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraFactoredLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1Libra
open CuSavingsLibraSourceModel CuSavingsLibraSourceControl OccupancyRangeTraversal
open CuSavingsLibraSourceFactored CuSavingsLibraSourcePrepare CuSavingsLibraSourceArrays
open CuSavingsLibraSourceSides
variable {R S : Type} [CommSemiring R] [CommSemiring S] [Shared]
variable (A : Arithmetic R S)
abbrev Extra := Array K 2#usize
abbrev State := Range × Points

def body (ap0 ap1 : Points) (extra : Extra) : State → Result (ControlFlow State Points)
  | (iter,weights) => new.factored_s2_libra_weights_loop.body ap0 ap1 extra iter weights

private theorem source_step (ap0 ap1 : Points) (extra : Extra)
    (iter iter1 : Range) (weights : Points)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some iter.start,iter1)) :
    body ap0 ap1 extra (iter,weights)=(do
      let q ← Array.index_usize extra iter.start
      let data ← prepare ap0 ap1 q
      if iter.start=0#usize then
        let result ← side0 data weights
        .ok (@ControlFlow.cont State Points (iter1,result))
      else
        let result ← side1 ap1 data weights
        .ok (@ControlFlow.cont State Points (iter1,result))) := by
  unfold body
  dsimp only
  rw [body_factor,hnext]
  rfl

private theorem replicate_getD {T : Type} (x : T) (n i : Nat) :
    ((List.replicate n x)[i]?).getD x=x := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

private theorem zero_lookup (i : Nat) :
    lookup (Array.repeat 4#usize field.wide_exact.WideExact.ZERO) field.wide_exact.WideExact.ZERO i=
      field.wide_exact.WideExact.ZERO := by
  simpa only [lookup,Array.repeat,List.getD_eq_getElem?_getD] using
    replicate_getD field.wide_exact.WideExact.ZERO (4#usize).val i

private theorem second_congr (ap0 ap1 : Points) (q : K) (f g : Nat → R)
    (h : ∀ i,i<4 → f i=g i) (j : Nat) (hj : j<4) :
    second A ap0 ap1 q f j=second A ap0 ap1 q g j := by
  unfold second
  by_cases h3 : j=3
  · simp only [h3,↓reduceIte]
  · by_cases h2 : j=2
    · simp only [h2,↓reduceIte]
    · by_cases h1 : j=1
      · simp only [h3,h2,h1,↓reduceIte,h 1 (by omega)]
      · simp only [h3,h2,h1,↓reduceIte,h j hj]

def combined (ap0 ap1 : Points) (extra : Extra) (j : Nat) : R :=
  second A ap0 ap1 (lookup extra field.QM31.ONE 1)
    (first A ap0 ap1 (lookup extra field.QM31.ONE 0) (fun _ => 0)) j

theorem two_steps_success (ap0 ap1 : Points) (extra : Extra)
    (hp0 : ∀ i,i<4 → A.canonicalE (lookup ap0 field.wide_exact.WideExact.ZERO i))
    (hp1 : ∀ i,i<4 → A.canonicalE (lookup ap1 field.wide_exact.WideExact.ZERO i))
    (he : ∀ i,i<2 → A.canonicalK (lookup extra field.QM31.ONE i)) :
    ∃ weights,new.factored_s2_libra_weights ap0 ap1 extra=.ok weights ∧ Canonical A weights ∧
      ∀ j,j<4 → decoded A weights j=combined A ap0 ap1 extra j := by
  let initial : Points := Array.repeat 4#usize field.wide_exact.WideExact.ZERO
  let iter0 : Range := {start:=0#usize,«end»:=2#usize}
  obtain ⟨iter1,hnext0,hstart1,hend1,_⟩ := next_step iter0 (by scalar_tac)
  have hs1 : iter1.start.val=1 := by simpa only [iter0,show (0#usize).val=0 by scalar_tac,Nat.zero_add] using hstart1
  have he1 : iter1.«end»=2#usize := hend1
  obtain ⟨iter2,hnext1,hstart2,hend2,_⟩ := next_step iter1 (by rw [he1];scalar_tac)
  have hs2 : iter2.start.val=2 := by omega
  have he2 : iter2.«end»=2#usize := hend2.trans he1
  have hdone := next_done iter2 (by rw [he2];scalar_tac)
  have hn1 : iter1.start≠0#usize := by
    intro hz
    have hv : iter1.start.val=0 := by rw [hz];scalar_tac
    omega
  have hread0 := read extra field.QM31.ONE 0#usize (by scalar_tac)
  have hread1 := read extra field.QM31.ONE iter1.start (by scalar_tac)
  simp only [show (0#usize).val=0 by scalar_tac] at hread0
  simp only [hs1] at hread1
  obtain ⟨data0,hprepare0,hd0⟩ := CuSavingsLibraSourcePrepare.source_success A ap0 ap1
    (lookup extra field.QM31.ONE 0) hp0 hp1 (he 0 (by omega))
  obtain ⟨data1,hprepare1,hd1⟩ := CuSavingsLibraSourcePrepare.source_success A ap0 ap1
    (lookup extra field.QM31.ONE 1) hp0 hp1 (he 1 (by omega))
  have hiC : Canonical A initial := by
    intro i _
    change A.canonicalE (lookup (Array.repeat 4#usize field.wide_exact.WideExact.ZERO) field.wide_exact.WideExact.ZERO i)
    rw [zero_lookup]
    exact A.zero
  have hiV : decoded A initial=(fun _ => 0) := by
    funext i
    unfold decoded
    change A.decodeE (lookup (Array.repeat 4#usize field.wide_exact.WideExact.ZERO) field.wide_exact.WideExact.ZERO i)=0
    rw [zero_lookup]
    exact A.zero_value
  obtain ⟨weights0,hside0,hc0,hv0⟩ := side0_success A ap0 ap1 (lookup extra field.QM31.ONE 0) data0 initial hd0 hiC
  obtain ⟨weights1,hside1,hc1,hv1⟩ := side1_success A ap0 ap1 (lookup extra field.QM31.ONE 1) data1 weights0 hd1 hc0 hp1
  have hb0 : body ap0 ap1 extra (iter0,initial)=.ok (.cont (iter1,weights0)) := by
    rw [source_step ap0 ap1 extra iter0 iter1 initial hnext0,hread0]
    simp only [bind_tc_ok]
    rw [hprepare0]
    simp only [bind_tc_ok,show iter0.start=0#usize from rfl,↓reduceIte]
    rw [hside0]
    rfl
  have hb1 : body ap0 ap1 extra (iter1,weights0)=.ok (.cont (iter2,weights1)) := by
    rw [source_step ap0 ap1 extra iter1 iter2 weights0 hnext1,hread1]
    simp only [bind_tc_ok]
    rw [hprepare1]
    simp only [bind_tc_ok,hn1,↓reduceIte]
    rw [hside1]
    rfl
  have hb2 : body ap0 ap1 extra (iter2,weights1)=.ok (.done weights1) := by
    unfold body
    dsimp only
    rw [body_factor,hdone]
    rfl
  have hrun : execute (body ap0 ap1 extra) (iter0,initial)=.ok weights1 := by
    rw [execute_unroll,hb0]
    change execute (body ap0 ap1 extra) (iter1,weights0)=.ok weights1
    rw [execute_unroll,hb1]
    change execute (body ap0 ap1 extra) (iter2,weights1)=.ok weights1
    rw [execute_unroll,hb2]
    rfl
  refine ⟨weights1,?_,hc1,?_⟩
  · unfold new.factored_s2_libra_weights new.factored_s2_libra_weights_loop
    exact hrun
  · intro j hj
    rw [hv1 j hj]
    apply second_congr A ap0 ap1 (lookup extra field.QM31.ONE 1) _ _ _ j hj
    intro i hi
    rw [hv0 i hi,hiV]

def challenge (extra : Extra) (side : Nat) : R := A.embedding (A.decodeK (lookup extra field.QM31.ONE side))
def tupleAt (values : R × R × R × R) (j : Nat) : R :=
  if j=0 then values.1 else if j=1 then values.2.1 else if j=2 then values.2.2.1 else values.2.2.2

def value (ap0 ap1 : Points) (extra : Extra) (j : Nat) : R :=
  tupleAt (CuSavingsLibra.factoredWeights (point A ap0) (point A ap1) A.quarter
    (challenge A extra 0) (challenge A extra 1)) j

theorem combined_eq_factored (ap0 ap1 : Points) (extra : Extra) (j : Nat) (hj : j<4) :
    combined A ap0 ap1 extra j=value A ap0 ap1 extra j := by
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  have hp : (challenge A extra 1)^20=(challenge A extra 1)^16*(challenge A extra 1)^4 := by
    rw [show (20:Nat)=16+4 from rfl,pow_add]
  rcases hc with h|h|h|h <;> subst j <;>
    simp only [combined,first,second,value,tupleAt,CuSavingsLibra.factoredWeights,
      lowValue,highTerm,challenge,↓reduceIte]
  all_goals try rfl
  exact congrArg (fun x => _*x) hp

theorem source_success (ap0 ap1 : Points) (extra : Extra)
    (hp0 : ∀ i,i<4 → A.canonicalE (lookup ap0 field.wide_exact.WideExact.ZERO i))
    (hp1 : ∀ i,i<4 → A.canonicalE (lookup ap1 field.wide_exact.WideExact.ZERO i))
    (he : ∀ i,i<2 → A.canonicalK (lookup extra field.QM31.ONE i)) :
    ∃ weights,new.factored_s2_libra_weights ap0 ap1 extra=.ok weights ∧ Canonical A weights ∧
      ∀ j,j<4 → decoded A weights j=value A ap0 ap1 extra j := by
  obtain ⟨weights,hweights,hcanonical,hvalues⟩ := two_steps_success A ap0 ap1 extra hp0 hp1 he
  refine ⟨weights,hweights,hcanonical,?_⟩
  intro j hj
  exact (hvalues j hj).trans (combined_eq_factored A ap0 ap1 extra j hj)

#print axioms two_steps_success
#print axioms combined_eq_factored
#print axioms source_success
end AspisR1.CuSavingsLibraFactoredLoop
