import S9ActiveFourValueStepV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ActiveFourValueLoopV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeS3WeightBodyV1 (W Can decode)
open AspisR1S9ActiveFourCanonicalV1 (Parts Libra R)
open AspisR1S9ActiveFourValueStepV1 (cell4 libraValue E)
open AspisR1S9NativeS3CoefficientBodyV1 (C)

def activePrefix (input : Nat → E) (libra : Libra) : Nat → E
  | 0 => 0
  | n+1 => activePrefix input libra n+input n*libraValue libra n

theorem active_prefix_step (input : Nat → E) (libra : Libra) (n : Nat) :
    activePrefix input libra (n+1)=activePrefix input libra n+input n*libraValue libra n := rfl

private theorem bind_success {A B : Type} (m : Result A) (next : A → Result B) (out : B)
    (h : (do let x ← m;next x)=.ok out) : ∃ x,m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h;cases h
  | div => simp only [bind_tc_div] at h;cases h
  | ok x => exact ⟨x,rfl,h⟩

private theorem done_next_none (f : Slice U8) (libra : Libra) (iter : R) (parts out : Parts)
    (h : weights.Weights.pair_loop8.body f libra iter parts=.ok (.done out)) :
    ∃ iter1,core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (none,iter1) := by
  unfold weights.Weights.pair_loop8.body at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨opt,iterNext⟩
  cases opt with
  | none => exact ⟨iterNext,hn⟩
  | some j =>
    obtain ⟨carry,hcarry,h⟩ := bind_success _ _ _ h
    obtain ⟨value,hfield,h⟩ := bind_success _ _ _ h
    obtain ⟨coefficient,hcf,h⟩ := bind_success _ _ _ h
    obtain ⟨product,hmul,h⟩ := bind_success _ _ _ h
    obtain ⟨total,hadd,h⟩ := bind_success _ _ _ h
    obtain ⟨updated,hu,h⟩ := bind_success _ _ _ h
    cases h

/-- SAME native active4 run adds its exact field/coefficient products to the
incoming cell4. Its data stream comes from SAME f/coefficient run; input
libra/carry canonicality remain guards, with all products/sums internal. -/
theorem active_loop_same_input_prefix (f : Slice U8) (coefficients : C)
    (hbytes : 2048≤f.val.length)
    (hcoeff : weights.s2_grouped_inactive_pair_loop0 {start:=0#usize,«end»:=64#usize} f
      (Array.repeat 12#usize aspis_core.field.wide_exact.WideExact.ZERO)=.ok coefficients)
    (libra : Libra) (initial final : Parts)
    (hcarry : Can (cell4 initial))
    (hlibra : AspisR1S9NativeArrayCanonicalV1.ReadsCanonical libra)
    (hloop : weights.Weights.pair_loop8 {start:=0#usize,«end»:=4#usize} f initial libra=.ok final) :
    Can (cell4 final) ∧ decode (cell4 final)=decode (cell4 initial)+
      activePrefix (AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients hbytes hcoeff) libra 4 := by
  let input := AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients hbytes hcoeff
  let step := fun s : R × Parts=>weights.Weights.pair_loop8.body f libra s.1 s.2
  let inv := fun s : R × Parts=>s.1.end.val=4 ∧ s.1.start.val≤4 ∧ Can (cell4 s.2) ∧
    decode (cell4 s.2)=decode (cell4 initial)+activePrefix input libra s.1.start.val
  let measure := fun s : R × Parts=>s.1.end.val-s.1.start.val
  have hd : ∀ s result,inv s → step s=.ok (.done result) →
      Can (cell4 result) ∧ decode (cell4 result)=decode (cell4 initial)+activePrefix input libra 4 := by
    rintro ⟨r,c⟩ result ⟨he,hs,hcan,hmeaning⟩ hb
    obtain ⟨r1,hn⟩ := done_next_none f libra r c result hb
    have hstop := AspisR1S9StatementSourceLoopFactsV1.next_none_stop r r1 hn
    change r.end.val=4 at he
    change r.start.val≤4 at hs
    have hstart : r.start.val=4 := by omega
    have hout := AspisR1S9ActiveFourCanonicalV1.body_done_same f libra r c result hb
    subst result
    change decode (cell4 c)=decode (cell4 initial)+activePrefix input libra r.start.val at hmeaning
    exact ⟨hcan,by simpa only [hstart] using hmeaning⟩
  have hc : ∀ s s',inv s → step s=.ok (.cont s') → inv s' := by
    rintro ⟨r,c⟩ ⟨r1,c1⟩ ⟨he,hs,hcan,hmeaning⟩ hb
    change r.end.val=4 at he
    change r.start.val≤4 at hs
    change decode (cell4 c)=decode (cell4 initial)+activePrefix input libra r.start.val at hmeaning
    obtain ⟨j,hn,hj4,cout,hvalue⟩ := AspisR1S9ActiveFourValueStepV1.active_cont_same_input_value
      f coefficients hbytes hcoeff libra r r1 c c1 (by omega) hcan hlibra hb
    obtain ⟨hj,hlt,hadvance,hend⟩ := AspisR1S9ActualDotRangeBoundsV1.range_next_index_bounds r r1 j hn
    have hjval : j.val=r.start.val := congrArg (fun x : Usize=>x.val) hj
    have hend1 : r1.end.val=4 := by rw [hend];exact he
    have hstart1 : r1.start.val≤4 := by omega
    have hnext : decode (cell4 c1)=decode (cell4 initial)+activePrefix input libra r1.start.val := by
      rw [hadvance,active_prefix_step]
      calc
        decode (cell4 c1)=decode (cell4 c)+input j.val*libraValue libra j.val := hvalue
        _ = decode (cell4 initial)+activePrefix input libra r.start.val+
            input r.start.val*libraValue libra r.start.val := by rw [hmeaning,hjval]
        _ = _ := add_assoc _ _ _
    exact ⟨hend1,hstart1,cout,hnext⟩
  have hm : ∀ s s',step s=.ok (.cont s') → measure s'<measure s := by
    rintro ⟨r,c⟩ ⟨r1,c1⟩ hb
    obtain ⟨j,carry,value,coefficient,product,total,hn,hcarryRead,hfield,hcf,hmul,hadd,hu⟩ :=
      AspisR1S9ActiveFourCanonicalV1.body_cont_source f libra r r1 c c1 hb
    obtain ⟨hlt,hj,hstart,hend⟩ :=
      AspisR1S9ConstructorV3Loop2InnerCanonicalV1.next_some_progress r r1 j hn
    simp only [measure,hstart,hend]
    omega
  have hinit : inv ({start:=0#usize,«end»:=4#usize},initial) := by
    refine ⟨rfl,by change 0≤4;decide,hcarry,?_⟩
    change decode (cell4 initial)=decode (cell4 initial)+activePrefix input libra 0
    rw [activePrefix,add_zero]
  have hl : Aeneas.Std.loop step ({start:=0#usize,«end»:=4#usize},initial)=.ok final := hloop
  exact AspisR1S9LoopInvariantPropertyV1.loop_invariant_property step measure inv
    (fun result=>Can (cell4 result) ∧ decode (cell4 result)=decode (cell4 initial)+activePrefix input libra 4)
    hd hc hm _ final hinit hl

theorem unshared_active_loop_same_input_prefix (f : Slice U8) (coefficients : C)
    (hbytes : 2048≤f.val.length)
    (hcoeff : weights.s2_grouped_inactive_pair_loop0 {start:=0#usize,«end»:=64#usize} f
      (Array.repeat 12#usize aspis_core.field.wide_exact.WideExact.ZERO)=.ok coefficients)
    (libra : Libra) (initial final : Parts)
    (hcarry : Can (cell4 initial))
    (hlibra : AspisR1S9NativeArrayCanonicalV1.ReadsCanonical libra)
    (hloop : weights.Weights.pair_loop16 {start:=0#usize,«end»:=4#usize} f initial libra=.ok final) :
    Can (cell4 final) ∧ decode (cell4 final)=decode (cell4 initial)+
      activePrefix (AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients hbytes hcoeff) libra 4 := by
  rw [AspisR1S9ActiveFourCanonicalV1.unshared_active_eq] at hloop
  exact active_loop_same_input_prefix f coefficients hbytes hcoeff libra initial final hcarry hlibra hloop

#print axioms active_prefix_step
#print axioms active_loop_same_input_prefix
#print axioms unshared_active_loop_same_input_prefix
end AspisR1S9ActiveFourValueLoopV1
