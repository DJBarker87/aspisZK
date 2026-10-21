import S5QRaw.EbyKPushDecodedProductUpdateV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1DotCountBoundV1
open AspisR1DotPushLocal.Proof

def sumsBelowCount (k : Nat) (s : Array U64 4#usize) : Prop :=
  ∀ j : Nat, ∀ hj : j < 4,
    (s.val[j]'(by rw [s.property]; exact hj)).val ≤ k * 2 ^ 34

theorem updatedSums_below_succ_count
    (k : Nat) (s r : Array U64 4#usize)
    (hcount : k < 4096)
    (hs : sumsBelowCount k s) :
    sumsBelowCount (k+1) (updatedSums s r) := by
  intro j hj
  have hjs : j < s.val.length := by rw [s.property]; exact hj
  have hjr : j < r.val.length := by rw [r.property]; exact hj
  have hold := hs j hj
  have h4096 : 4096 * 2^34 = 2^46 := by norm_num
  have hk46 : k * 2^34 < 2^46 := by omega
  have hold46 : (s.val[j]'hjs).val < 2^46 := by omega
  have hstep := (updateWord_value (s.val[j]'hjs) (r.val[j]'hjr) hold46).1
  have hraw : (r.val[j]'hjr).val < 2^64 := (r.val[j]'hjr).bv.isLt
  have hfold := AspisR1EbyKDotPushNatStep.foldedRaw_lt_two34 hraw
  have hval : ((updatedSums s r).val[j]'(by rw [(updatedSums s r).property]; exact hj)).val =
      (s.val[j]'hjs).val + AspisR1EbyKDotPushNatStep.foldedRaw (r.val[j]'hjr).val := by
    simpa only [updatedSums, List.getElem_zipWith] using hstep
  rw [hval]
  dsimp [sumsBelowCount]
  omega

 theorem count_bound_to_preaccumulator
    (k : Nat) (s : Array U64 4#usize)
    (hk : k < 4096) (hs : sumsBelowCount k s) :
    ∀ j : Nat, ∀ hj : j < 4,
      (s.val[j]'(by rw [s.property]; exact hj)).val < 2 ^ 46 := by
  intro j hj
  have h := hs j hj
  have h4096 : 4096 * 2^34 = 2^46 := by norm_num
  have hk46 : k * 2^34 < 2^46 := by omega
  omega

 theorem successful_push_preserves_count_bound
    (rawFn : AspisR1EbyKPushDotBackend.RawFn)
    (self : AspisR1EbyKPushDotBackend.PushState)
    (value : AspisR1EbyKPushDotBackend.PushWide)
    (scalar : AspisR1EbyKPushDotBackend.PushQm)
    (out : AspisR1EbyKPushDotBackend.PushState)
    (h0 : sumsBelowCount self.count.val self.c0.sums)
    (h1 : sumsBelowCount self.count.val self.c1.sums)
    (hrun : AspisR1EbyKPushDotBackend.pushWithDotBackend rawFn self value scalar =
      .ok (.Ok (), out)) :
    sumsBelowCount out.count.val out.c0.sums ∧
    sumsBelowCount out.count.val out.c1.sums ∧
    out.count.val ≤ 4096 ∧
    (∀ j : Nat, ∀ hj : j < 4, (self.c0.sums.val[j]'(by rw [self.c0.sums.property]; exact hj)).val < 2^46) ∧
    (∀ j : Nat, ∀ hj : j < 4, (self.c1.sums.val[j]'(by rw [self.c1.sums.property]; exact hj)).val < 2^46) := by
  obtain ⟨lo,hi,hlo,hhi,h0state,h1state,hcount,hinc,_⟩ :=
    AspisR1EbyKPushDotBackend.successful_push_exact_backend rawFn self value scalar out hrun
  have hcountval : self.count.val < 4096 := by
    simpa [AspisR1EbyKPushExplicitOpsV1.maxTerms] using hcount
  have h0pre := count_bound_to_preaccumulator self.count.val self.c0.sums hcountval h0
  have h1pre := count_bound_to_preaccumulator self.count.val self.c1.sums hcountval h1
  have h0next := updatedSums_below_succ_count self.count.val self.c0.sums lo hcountval h0
  have h1next := updatedSums_below_succ_count self.count.val self.c1.sums hi hcountval h1
  constructor
  · rw [hinc, h0state]; exact h0next
  constructor
  · rw [hinc, h1state]; exact h1next
  constructor
  · rw [hinc]
    exact Nat.add_one_le_iff.mpr hcountval
  exact ⟨h0pre,h1pre⟩


inductive AcceptedPushTrace (rawFn : AspisR1EbyKPushDotBackend.RawFn) :
    AspisR1EbyKPushDotBackend.PushState →
    List (AspisR1EbyKPushDotBackend.PushWide × AspisR1EbyKPushDotBackend.PushQm) →
    AspisR1EbyKPushDotBackend.PushState → Prop where
  | nil (s) : AcceptedPushTrace rawFn s [] s
  | cons (s mid out v q xs)
      (hpush : AspisR1EbyKPushDotBackend.pushWithDotBackend rawFn s v q =
        .ok (.Ok (), mid))
      (htail : AcceptedPushTrace rawFn mid xs out) :
      AcceptedPushTrace rawFn s ((v,q)::xs) out

theorem accepted_trace_preserves_count_bound
    (rawFn : AspisR1EbyKPushDotBackend.RawFn)
    (start finish : AspisR1EbyKPushDotBackend.PushState)
    (xs : List (AspisR1EbyKPushDotBackend.PushWide × AspisR1EbyKPushDotBackend.PushQm))
    (h0 : sumsBelowCount start.count.val start.c0.sums)
    (h1 : sumsBelowCount start.count.val start.c1.sums)
    (hstartCount : start.count.val ≤ 4096)
    (htrace : AcceptedPushTrace rawFn start xs finish) :
    sumsBelowCount finish.count.val finish.c0.sums ∧
    sumsBelowCount finish.count.val finish.c1.sums ∧
    finish.count.val ≤ 4096 := by
  induction htrace with
  | nil s => exact ⟨h0,h1,hstartCount⟩
  | @cons s mid finish v q xs hpush htail ih =>
      have hbefore := successful_push_preserves_count_bound rawFn s v q mid h0 h1 hpush
      have hmidCount : mid.count.val ≤ 4096 := hbefore.2.2.1
      exact ih hbefore.1 hbefore.2.1 hmidCount

#print axioms updatedSums_below_succ_count
#print axioms count_bound_to_preaccumulator
#print axioms successful_push_preserves_count_bound
#print axioms accepted_trace_preserves_count_bound
end AspisR1DotCountBoundV1
