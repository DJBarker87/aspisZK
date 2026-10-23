import S9ActualLow16BodyTraceV1
import S9NativeLowScalarArithmeticV1
import S9NativeArrayCanonicalV1
import S9FactorArrayEntryV1
import S9ConstructorV3Loop2InnerCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualLow16BodyMeaningV1
open AspisR1S9ActualLow16BodyTraceV1
open AspisR1S9NativeLowScalarArithmeticV1
open AspisR1S9NativeWideDecodedArithmeticV1 (decode Canonical)
open AspisR1S9FactorArrayEntryV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1 (index_success_bound)
abbrev GoodPowers (a : Powers) : Prop := AspisR1S9NativeArrayCanonicalV1.ReadsCanonical a

def permutedIndex (n : Nat) : Nat := [0,3,2,1].getD n 0

def powerValue (a : Powers) (n : Nat) : E :=
  match a.val[n]? with
  | none => 0
  | some x => decode x

def expectedLow (ap0 ap1 : Powers) (s : Nat) : E :=
  (powerValue ap0 (permutedIndex (s%4))*powerValue ap1 (permutedIndex (s/4)))*
    (embed weights.QUARTER*embed weights.QUARTER)

theorem power_value_read (a : Powers) (i : Usize) (x : W)
    (h : Array.index_usize a i=.ok x) : powerValue a i.val=decode x := by
  have hi := index_success_bound a i x h
  have he := accepted_index_eq_atN a i hi x h
  have hb : i.val<a.val.length := by simpa only [a.property] using hi
  unfold powerValue
  rw [List.getElem?_eq_getElem hb]
  exact congrArg decode he.symm

theorem permuted_index_read (i j : Usize)
    (h : Array.index_usize weights.PERM i=.ok j) : j.val=permutedIndex i.val := by
  have hi := index_success_bound weights.PERM i j h
  have h4 : (4#usize).val=4 := rfl
  rw [h4] at hi
  have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
  rcases hc with h0 | h1 | h2 | h3
  · have e : i=0#usize := UScalar.eq_of_val_eq h0
    subst i
    have hr : Array.index_usize weights.PERM 0#usize=.ok (0#usize) := by
      unfold weights.PERM
      rfl
    have ej : j=0#usize := Result.ok.inj (h.symm.trans hr)
    rw [ej]; rfl
  · have e : i=1#usize := UScalar.eq_of_val_eq h1
    subst i
    have hr : Array.index_usize weights.PERM 1#usize=.ok (3#usize) := by
      unfold weights.PERM
      rfl
    have ej : j=3#usize := Result.ok.inj (h.symm.trans hr)
    rw [ej]; rfl
  · have e : i=2#usize := UScalar.eq_of_val_eq h2
    subst i
    have hr : Array.index_usize weights.PERM 2#usize=.ok (2#usize) := by
      unfold weights.PERM
      rfl
    have ej : j=2#usize := Result.ok.inj (h.symm.trans hr)
    rw [ej]; rfl
  · have e : i=3#usize := UScalar.eq_of_val_eq h3
    subst i
    have hr : Array.index_usize weights.PERM 3#usize=.ok (1#usize) := by
      unfold weights.PERM
      rfl
    have ej : j=1#usize := Result.ok.inj (h.symm.trans hr)
    rw [ej]; rfl

theorem div_four_value (s q : Usize) (h : (s/4#usize : Result Usize)=.ok q) : q.val=s.val/4 := by
  obtain ⟨q',hq,hvalue⟩ := UScalar.div_spec s (y:=4#usize) (by decide)
  have he : q'=q := Result.ok.inj (hq.symm.trans h)
  subst q'
  have h4 : (4#usize).val=4 := rfl
  simpa only [h4] using hvalue

theorem rem_four_value (s r : Usize) (h : (s%4#usize : Result Usize)=.ok r) : r.val=s.val%4 := by
  obtain ⟨r',hr,hvalue⟩ := WP.spec_imp_exists (UScalar.rem_spec s (y:=4#usize) (by decide))
  have he : r'=r := Result.ok.inj (hr.symm.trans h)
  subst r'
  have h4 : (4#usize).val=4 := rfl
  simpa only [h4] using hvalue

theorem low_body_cont_meaning (ap0 ap1 : Powers) (iter iterNext : Iter)
    (low lowNext : Low) (hp0 : GoodPowers ap0) (hp1 : GoodPowers ap1)
    (h : weights.Weights.pair_loop15.body ap0 ap1 iter low=.ok (.cont (iterNext,lowNext))) :
    ∃ (s : Usize) (value : W),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some s,iterNext) ∧
      Array.update low s value=.ok lowNext ∧ Canonical value ∧ decode value=expectedLow ap0 ap1 s.val := by
  rcases low_body_success_trace ap0 ap1 iter low _ h with hd | hc
  · obtain ⟨it,hn,he⟩ := hd; cases he
  · obtain ⟨s,it,lo,pi,hi,pj,x,y,product,value,m,next,
      hn,hl,hpi,hx,hh,hpj,hy,hprod,hm,hvalue,hu,he⟩ := hc
    have ep : (iterNext,lowNext)=(it,next) := ControlFlow.cont.inj he
    cases ep
    obtain ⟨cp,vp⟩ := AspisR1S9NativeWideDecodedArithmeticV1.actual_mul_success_decoded
      x y product (hp0 pi x hx) (hp1 pj y hy) hprod
    obtain ⟨cv,vv⟩ := native_mul_m31_success product value m cp hvalue
    have hquarter := native_quarter_square_embedding m hm
    have elo := rem_four_value s lo hl
    have ehi := div_four_value s hi hh
    have epi := permuted_index_read lo pi hpi
    have epj := permuted_index_read hi pj hpj
    have vx := power_value_read ap0 pi x hx
    have vy := power_value_read ap1 pj y hy
    rw [elo] at epi
    rw [ehi] at epj
    rw [epi] at vx
    rw [epj] at vy
    refine ⟨s,value,hn,hu,cv,?_⟩
    rw [vv,vp,hquarter]
    unfold expectedLow
    rw [vx,vy]

#print axioms power_value_read
#print axioms permuted_index_read
#print axioms div_four_value
#print axioms rem_four_value
#print axioms low_body_cont_meaning
end AspisR1S9ActualLow16BodyMeaningV1
