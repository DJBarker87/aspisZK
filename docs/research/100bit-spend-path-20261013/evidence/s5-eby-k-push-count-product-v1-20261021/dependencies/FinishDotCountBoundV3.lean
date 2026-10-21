import FinishDotLoopCount
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishDotCountBoundV2
open AspisR1FinishDotConcreteOps AspisR1FinishDotSourceABI AspisR1FinishRelationCurrent AspisR1CurrentWide.Proof
open AspisR1DotPushLocal.Proof

def sumsBelowCount (k : Nat) (s : Array U64 4#usize) : Prop :=
  ∀ j : Nat, ∀ hj : j < 4,
    (s.val[j]'(by rw [s.property]; exact hj)).val ≤ k * 2 ^ 34

theorem updatedSums_below_succ_count
    (k : Nat) (s r : Array U64 4#usize) (hcount : k < 4096)
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
    (self : AspisR1EbyKPushDotBackend.PushState) (value : AspisR1EbyKPushDotBackend.PushWide) (scalar : AspisR1EbyKPushDotBackend.PushQm) (out : AspisR1EbyKPushDotBackend.PushState)
    (h0 : sumsBelowCount self.count.val self.c0.sums)
    (h1 : sumsBelowCount self.count.val self.c1.sums)
    (hrun : AspisR1EbyKPushDotBackend.pushWithDotBackend rawFn self value scalar = .ok (.Ok (),out)) :
    sumsBelowCount out.count.val out.c0.sums ∧
    sumsBelowCount out.count.val out.c1.sums ∧ out.count.val ≤ 4096 ∧
    (∀ j : Nat, ∀ hj : j < 4,
      (self.c0.sums.val[j]'(by rw [self.c0.sums.property]; exact hj)).val < 2^46) ∧
    (∀ j : Nat, ∀ hj : j < 4,
      (self.c1.sums.val[j]'(by rw [self.c1.sums.property]; exact hj)).val < 2^46) := by
  obtain ⟨lo,hi,hlo,hhi,h0state,h1state,hcount,hinc,_⟩ :=
    AspisR1EbyKPushDotBackend.successful_push_exact_backend rawFn self value scalar out hrun
  have hcountval : self.count.val < 4096 := by
    simpa [AspisR1EbyKPushExplicitOpsV1.maxTerms] using hcount
  have h0pre := count_bound_to_preaccumulator self.count.val self.c0.sums hcountval h0
  have h1pre := count_bound_to_preaccumulator self.count.val self.c1.sums hcountval h1
  have h0next := updatedSums_below_succ_count self.count.val self.c0.sums lo hcountval h0
  have h1next := updatedSums_below_succ_count self.count.val self.c1.sums hi hcountval h1
  constructor
  · rw [hinc,h0state]; exact h0next
  constructor
  · rw [hinc,h1state]; exact h1next
  constructor
  · rw [hinc]; exact Nat.add_one_le_iff.mpr hcountval
  exact ⟨h0pre,h1pre⟩

theorem invariant_step {W : Type}
    (base : AspisR1FinishRelationCurrent.FinishOps W AspisR1FinishDotSourceABI.PushState)
    (rawFn : AspisR1EbyKPushDotBackend.RawFn)
    (j j1 : Usize) (s s1 : AspisR1FinishDotSourceABI.PushState) (x : AspisR1CurrentWide.Proof.FinishE) (q : AspisR1CurrentWide.Proof.FinishQM)
    (hpush : (withConcreteDot base rawFn).pushDot s x q = .ok (.Ok (),s1))
    (hinc : j + 1#usize = ok j1)
    (hinv : sumsBelowCount j.val s.c0.sums ∧ sumsBelowCount j.val s.c1.sums ∧ s.count.val=j.val) :
    sumsBelowCount j1.val s1.c0.sums ∧ sumsBelowCount j1.val s1.c1.sums ∧ s1.count.val=j1.val := by
  have hpush' : AspisR1EbyKPushDotBackend.pushWithDotBackend rawFn s (toPushWide x) (toPushQM q) =
      .ok (.Ok (),s1) := by simpa [withConcreteDot] using hpush
  have h0 : sumsBelowCount s.count.val s.c0.sums := by simpa [hinv.2.2] using hinv.1
  have h1 : sumsBelowCount s.count.val s.c1.sums := by simpa [hinv.2.2] using hinv.2.1
  have hbound : sumsBelowCount s1.count.val s1.c0.sums ∧
      sumsBelowCount s1.count.val s1.c1.sums ∧ s1.count.val ≤ 4096 ∧
      (∀ k, ∀ hk : k < 4, (s.c0.sums.val[k]'(by rw [s.c0.sums.property]; exact hk)).val < 2^46) ∧
      (∀ k, ∀ hk : k < 4, (s.c1.sums.val[k]'(by rw [s.c1.sums.property]; exact hk)).val < 2^46) :=
    successful_push_preserves_count_bound rawFn s (toPushWide x) (toPushQM q) s1 h0 h1 hpush'
  obtain ⟨lo,hi,hlo,hhi,h0state,h1state,hguard,hcount,_⟩ :=
    AspisR1EbyKPushDotBackend.successful_push_exact_backend rawFn s (toPushWide x) (toPushQM q) s1 hpush'
  have hval := UScalar.add_equiv j 1#usize
  rw [hinc] at hval
  have hidx : j1.val=j.val+1 := hval.2.1
  have hsCount : s1.count.val=j1.val := by
    calc s1.count.val = s.count.val+1 := hcount
      _ = j.val+1 := by rw [hinv.2.2]
      _ = j1.val := hidx.symm
  have hpost0 := hbound.1
  have hpost1 := hbound.2.1
  rw [hsCount] at hpost0 hpost1
  exact ⟨hpost0,hpost1,hsCount⟩

theorem successful_concrete_query_dot_count_bound {W : Type}
    (base : AspisR1FinishRelationCurrent.FinishOps W AspisR1FinishDotSourceABI.PushState)
    (rawFn : AspisR1EbyKPushDotBackend.RawFn)
    (fm : Slice U8) (ws : Slice AspisR1FinishRelationCurrent.aspis_core.field.QM31)
    (out : AspisR1CurrentWide.Proof.FinishE)
    (hrun : AspisR1FinishRelationCurrent.verifier.finish_query_dot
      (withConcreteDot base rawFn) fm ws = .ok (.Ok out)) :
    ∃ final : AspisR1FinishDotSourceABI.PushState,
      final.count.val=ws.len.val ∧ AspisR1FinishDotSourceABI.finishFromPush final=.ok out ∧
      sumsBelowCount ws.len.val final.c0.sums ∧
      sumsBelowCount ws.len.val final.c1.sums := by
  obtain ⟨initial,final,hnew,hchain,hfinish⟩ :=
    AspisR1FinishRelationCurrent.FinishCandidateDotTrace.finish_success_trace
      (withConcreteDot base rawFn) fm ws out hrun
  have hzero : initial=EbyKNewToPushStateABI.pushZero :=
    Result.ok.inj (hnew.symm.trans sourceNewDot_zero)
  let Inv : Nat → AspisR1FinishDotSourceABI.PushState → Prop := fun j s =>
    sumsBelowCount j s.c0.sums ∧ sumsBelowCount j s.c1.sums ∧ s.count.val=j
  have hinitial : Inv 0 initial := by
    rw [hzero]
    refine ⟨?_,?_,rfl⟩
    · intro j hj
      have hcases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
      rcases hcases with h | h | h | h <;> subst j <;>
        simp [EbyKNewToPushStateABI.pushZero, sumsBelowCount]
    · intro j hj
      have hcases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
      rcases hcases with h | h | h | h <;> subst j <;>
        simp [EbyKNewToPushStateABI.pushZero, sumsBelowCount]
  have hfinal := AspisR1FinishRelationCurrent.FinishCandidateDotTrace.chain_invariant
    (withConcreteDot base rawFn) fm ws Inv (by
      intro j j1 s s1 x q hactive hread hweight hpush hinc hinv
      have hstep := invariant_step base rawFn j j1 s s1 x q hpush hinc hinv
      simpa using hstep) hchain hinitial
  exact ⟨final,hfinal.2.2,hfinish,hfinal.1,hfinal.2.1⟩

#print axioms successful_concrete_query_dot_count_bound
end AspisR1FinishDotCountBoundV2

