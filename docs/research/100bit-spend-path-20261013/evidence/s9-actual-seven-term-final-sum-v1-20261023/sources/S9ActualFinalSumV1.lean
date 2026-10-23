import S9NativeWideDecodedArithmeticV1
import S9FactorArrayEntryV1
import S9StatementSourceLoopFactsV1
import S9LoopInvariantPropertyV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ActualFinalSumV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeWideDecodedArithmeticV1
open AspisR1S9FactorArrayEntryV1
abbrev R := core.ops.range.Range Usize
abbrev A := Array W 7#usize

def Good (a : A) : Prop :=
  ∀ (i : Usize) (w : W), Array.index_usize a i=.ok w → Canonical w

def term (parts k : A) (i : Nat) : AspisWideTower.WideExact :=
  if h : i<7 then
    decode (k.val[i]'(by rw [k.property]; exact h))*
      decode (parts.val[i]'(by rw [parts.property]; exact h))
  else 0

def partialSum (parts k : A) (n : Nat) : AspisWideTower.WideExact :=
  ∑ i ∈ Finset.range n, term parts k i

private theorem bind_success {X Y : Type} (m : Result X) (next : X → Result Y) (out : Y)
    (h : (do let x ← m; next x)=.ok out) : ∃ x, m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- The actual final sum step supplies its own source reads, multiplication,
addition, and exact decoded update. All arithmetic input guards are stated. -/
theorem actual_body_cont (parts k : A) (iter iterOut : R) (acc out : W)
    (hp : Good parts) (hk : Good k) (ha : Canonical acc)
    (h : weights.Weights.pair_loop17.body parts k iter acc=.ok (.cont (iterOut,out))) :
    ∃ (i : Usize) (p q product : W),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some i,iterOut) ∧
      Array.index_usize parts i=.ok p ∧ Array.index_usize k i=.ok q ∧
      aspis_core.field.wide_exact.WideExact.mul q p=.ok product ∧
      aspis_core.field.wide_exact.WideExact.add acc product=.ok out ∧
      Canonical out ∧ decode out=decode acc+decode q*decode p := by
  unfold weights.Weights.pair_loop17.body at h
  simp only [trace.value,bind_tc_ok] at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨opt,iterNext⟩
  cases opt with
  | none => cases h
  | some i =>
    obtain ⟨p,hrp,h⟩ := bind_success _ _ _ h
    obtain ⟨q,hrq,h⟩ := bind_success _ _ _ h
    obtain ⟨product,hm,h⟩ := bind_success _ _ _ h
    obtain ⟨total,hs,h⟩ := bind_success _ _ _ h
    have he := ControlFlow.cont.inj (Result.ok.inj h)
    cases he
    obtain ⟨hproduct,hpm⟩ := actual_mul_success_decoded q p product (hk i q hrq) (hp i p hrp) hm
    obtain ⟨hout,hom⟩ := actual_add_success_decoded acc product out ha hproduct hs
    exact ⟨i,p,q,product,hn,hrp,hrq,hm,hs,hout,by rw [hom,hpm]⟩

theorem actual_body_done (parts k : A) (iter : R) (acc out : W)
    (h : weights.Weights.pair_loop17.body parts k iter acc=.ok (.done out)) :
    out=acc ∧ ∃ iterOut, core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=
      .ok (none,iterOut) := by
  unfold weights.Weights.pair_loop17.body at h
  simp only [trace.value,bind_tc_ok] at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨opt,iterNext⟩
  cases opt with
  | none =>
    have he := ControlFlow.done.inj (Result.ok.inj h)
    exact ⟨he.symm,iterNext,hn⟩
  | some i =>
    obtain ⟨p,hrp,h⟩ := bind_success _ _ _ h
    obtain ⟨q,hrq,h⟩ := bind_success _ _ _ h
    obtain ⟨product,hm,h⟩ := bind_success _ _ _ h
    obtain ⟨total,hs,h⟩ := bind_success _ _ _ h
    cases h

private theorem actual_body_cont_next (parts k : A) (iter iterOut : R) (acc out : W)
    (h : weights.Weights.pair_loop17.body parts k iter acc=.ok (.cont (iterOut,out))) :
    ∃ i, core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some i,iterOut) := by
  unfold weights.Weights.pair_loop17.body at h
  simp only [trace.value,bind_tc_ok] at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨opt,iterNext⟩
  cases opt with
  | none => cases h
  | some i =>
    obtain ⟨p,hrp,h⟩ := bind_success _ _ _ h
    obtain ⟨q,hrq,h⟩ := bind_success _ _ _ h
    obtain ⟨product,hm,h⟩ := bind_success _ _ _ h
    obtain ⟨total,hs,h⟩ := bind_success _ _ _ h
    have he := ControlFlow.cont.inj (Result.ok.inj h)
    cases he
    exact ⟨i,hn⟩

private theorem reads_term (parts k : A) (i : Usize) (p q : W) (hi : i.val<7)
    (hp : Array.index_usize parts i=.ok p) (hk : Array.index_usize k i=.ok q) :
    term parts k i.val=decode q*decode p := by
  have ep := accepted_index_eq_atN parts i hi p hp
  have eq := accepted_index_eq_atN k i hi q hk
  unfold atN at ep eq
  simp only [term,hi,↓reduceDIte]
  rw [←ep,←eq]

/-- Accepted-run sum semantics reuses the existing source-loop invariant
principle and the old S1 weighted-sum proof pattern. No child success is assumed. -/
theorem actual_final_sum_loop_success (parts k : A) (iter : R) (acc out : W)
    (hp : Good parts) (hk : Good k) (hend : iter.end=7#usize)
    (hi : iter.start.val≤7) (ha : Canonical acc)
    (hacc : decode acc=partialSum parts k iter.start.val)
    (hloop : weights.Weights.pair_loop17 iter parts k acc=.ok out) :
    Canonical out ∧ decode out=partialSum parts k 7 := by
  let step := fun s : R × W => weights.Weights.pair_loop17.body parts k s.1 s.2
  let inv := fun s : R × W => s.1.end=7#usize ∧ s.1.start.val≤7 ∧ Canonical s.2 ∧
    decode s.2=partialSum parts k s.1.start.val
  let measure := fun s : R × W => s.1.end.val-s.1.start.val
  let post := fun v : W => Canonical v ∧ decode v=partialSum parts k 7
  have hd : ∀ s v, inv s → step s=.ok (.done v) → post v := by
    rintro ⟨r,c⟩ v ⟨he,hle,hc,hm⟩ hb
    change r.end=7#usize at he
    change r.start.val≤7 at hle
    change Canonical c at hc
    change decode c=partialSum parts k r.start.val at hm
    obtain ⟨hv,r',hn⟩ := actual_body_done parts k r c v hb
    have hstop := AspisR1S9StatementSourceLoopFactsV1.next_none_stop r r' hn
    rw [he] at hstop
    have hz : r.start.val=7 := by change 7≤r.start.val at hstop; omega
    subst v
    exact ⟨hc,by simpa only [hz] using hm⟩
  have hc : ∀ s s', inv s → step s=.ok (.cont s') → inv s' := by
    rintro ⟨r,c⟩ ⟨r',c'⟩ ⟨he,hle,hcan,hmeaning⟩ hb
    change r.end=7#usize at he
    change r.start.val≤7 at hle
    change Canonical c at hcan
    change decode c=partialSum parts k r.start.val at hmeaning
    change r'.end=7#usize ∧ r'.start.val≤7 ∧ Canonical c' ∧
      decode c'=partialSum parts k r'.start.val
    obtain ⟨i,p,q,product,hn,hrp,hrq,hm,hs,hout,hdecode⟩ :=
      actual_body_cont parts k r r' c c' hp hk hcan hb
    obtain ⟨hlt,hival,hstart,hend'⟩ :=
      AspisR1S9ConstructorV3Loop2InnerCanonicalV1.next_some_progress r r' i hn
    have hrlt : r.start.val<7 := by rw [he] at hlt; exact hlt
    have hiv : i.val=r.start.val := congrArg (fun x : Usize => x.val) hival
    have hilt : i.val<7 := by omega
    have ht := reads_term parts k i p q hilt hrp hrq
    refine ⟨by rw [hend']; exact he,by omega,hout,?_⟩
    calc
      decode c'=decode c+term parts k i.val := by rw [hdecode,ht]
      _=partialSum parts k r.start.val+term parts k r.start.val := by rw [hmeaning,hival]
      _=partialSum parts k (r.start.val+1) := by simp only [partialSum,Finset.sum_range_succ]
      _=partialSum parts k r'.start.val := by rw [hstart]
  have hdec : ∀ s s', step s=.ok (.cont s') → measure s'<measure s := by
    rintro ⟨r,c⟩ ⟨r',c'⟩ hb
    obtain ⟨i,hn⟩ := actual_body_cont_next parts k r r' c c' hb
    obtain ⟨hlt,hival,hstart,hend'⟩ :=
      AspisR1S9ConstructorV3Loop2InnerCanonicalV1.next_some_progress r r' i hn
    simp only [measure,hstart,hend']
    omega
  have hinit : inv (iter,acc) := ⟨hend,hi,ha,hacc⟩
  have hl : Aeneas.Std.loop step (iter,acc)=.ok out := hloop
  exact AspisR1S9LoopInvariantPropertyV1.loop_invariant_property
    step measure inv post hd hc hdec _ out hinit hl

/-- The two admitted two-fold branches emit identical final-sum loops. -/
theorem shared_final_sum_eq (iter : R) (parts k : A) (acc : W) :
    weights.Weights.pair_loop9 iter parts k acc=
      weights.Weights.pair_loop17 iter parts k acc := by rfl

theorem actual_shared_final_sum_loop_success (parts k : A) (iter : R) (acc out : W)
    (hp : Good parts) (hk : Good k) (hend : iter.end=7#usize)
    (hi : iter.start.val≤7) (ha : Canonical acc)
    (hacc : decode acc=partialSum parts k iter.start.val)
    (hloop : weights.Weights.pair_loop9 iter parts k acc=.ok out) :
    Canonical out ∧ decode out=partialSum parts k 7 := by
  rw [shared_final_sum_eq] at hloop
  exact actual_final_sum_loop_success parts k iter acc out hp hk hend hi ha hacc hloop

#print axioms shared_final_sum_eq
#print axioms actual_shared_final_sum_loop_success
#print axioms actual_body_cont
#print axioms actual_body_done
#print axioms actual_final_sum_loop_success
end AspisR1S9ActualFinalSumV1
