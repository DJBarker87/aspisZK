import FinishDotCountBoundV3
import EbyKPushDotBackend
import AspisR1EbyKPushWideToQ

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

/- The source-selected Aeneas type declarations copied from the generated
`Types.lean`; their exact declaration bodies are checked against the pinned
generated file by the packet checker.  This avoids importing the generated
external-template module. -/
namespace AspisR1EbyEDotCutV1
abbrev field.M31 := Std.U32
structure field.CM31 where
  a : field.M31
  b : field.M31
structure field.QM31 where
  c0 : field.CM31
  c1 : field.CM31
structure field.wide_exact.WideExact where
  c0 : field.QM31
  c1 : field.QM31
abbrev fast_pairing.canonical.Q := Array Std.U32 4#usize
structure fast_pairing.canonical.Dot where
  sums : Array Std.U64 4#usize
structure fast_pairing.EbyEDot where
  ac : fast_pairing.canonical.Dot
  bd : fast_pairing.canonical.Dot
  ad : fast_pairing.canonical.Dot
  bc : fast_pairing.canonical.Dot
  count : Usize
end AspisR1EbyEDotCutV1

namespace AspisR1EbyEFourDotSourceStepV1

open AspisR1EbyKPushDotBackend
open AspisR1FinishDotCountBoundV2

abbrev Wide := AspisR1EbyEDotCutV1.field.wide_exact.WideExact
abbrev Q := AspisR1EbyEDotCutV1.fast_pairing.canonical.Q
abbrev Dot := AspisR1EbyEDotCutV1.fast_pairing.canonical.Dot
abbrev State := AspisR1EbyEDotCutV1.fast_pairing.EbyEDot
abbrev RawFn := AspisR1EbyKPushDotBackend.RawFn

def maxTerms : Usize := 4096#usize

/-- The generated source uses Aeneas' checked `Usize` addition at the final
count update. -/
def sourceAddUsize (a b : Usize) : Result Usize := (a + b : Result Usize)

def dotViaRawSource (rawFn : RawFn) (self : Dot) (a b : Q) : Result Dot := do
  let out ← AspisR1EbyKPushDotBackend.dotViaRaw rawFn ⟨self.sums⟩ a b
  .ok ⟨out.sums⟩

private theorem bind_ok_inv {α β : Type} (r : Result α) (f : α → Result β)
    (y : β) (h : Bind.bind r f = .ok y) :
    ∃ x, r = .ok x ∧ f x = .ok y := by
  cases r with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem dotViaRawSource_success (rawFn : RawFn) (self : Dot) (a b : Q) (out : Dot)
    (hrun : dotViaRawSource rawFn self a b = .ok out) :
    ∃ raw : Array U64 4#usize,
      rawFn a b = .ok raw ∧
      out.sums = AspisR1DotPushLocal.Proof.updatedSums self.sums raw := by
  unfold dotViaRawSource at hrun
  obtain ⟨d,hd,he⟩ := bind_ok_inv _ _ _ hrun
  have hdot : AspisR1EbyKPushDotBackend.dotViaRaw rawFn ⟨self.sums⟩ a b =
      .ok ⟨d.sums⟩ := by simpa using hd
  obtain ⟨raw,hraw,hstate⟩ :=
    AspisR1EbyKPushDotBackend.dotViaRaw_success rawFn ⟨self.sums⟩ a b ⟨d.sums⟩ hdot
  have hout : d.sums = out.sums := by
    have he' : (⟨d.sums⟩ : Dot) = out := Result.ok.inj he
    exact congrArg (fun x : Dot => x.sums) he'
  have hstate' : d.sums = AspisR1DotPushLocal.Proof.updatedSums self.sums raw := by
    simpa using hstate
  exact ⟨raw,hraw,by calc
    out.sums = d.sums := hout.symm
    _ = AspisR1DotPushLocal.Proof.updatedSums self.sums raw := hstate'⟩

/-- Source-shaped EbyEDot push body.  Its four `pushDot` calls are in the
original Rust order; `fromWide` and checked count addition remain explicit
callee boundaries. -/
def pushWithOps
    (fromWide : Wide → Result (Array Q 2#usize))
    (pushDot : Dot → Q → Q → Result Dot)
    (addUsize : Usize → Usize → Result Usize)
    (self : State) (left right : Wide) :
    Result ((core.result.Result Unit Unit) × State) := do
  if self.count >= maxTerms
  then ok (core.result.Result.Err (), self)
  else
    let a ← fromWide left
    let a1 ← Array.index_usize a 0#usize
    let b ← Array.index_usize a 1#usize
    let a2 ← fromWide right
    let c ← Array.index_usize a2 0#usize
    let d ← Array.index_usize a2 1#usize
    let d1 ← pushDot self.ac a1 c
    let d2 ← pushDot self.bd b d
    let d3 ← pushDot self.ad a1 d
    let d4 ← pushDot self.bc b c
    let i ← addUsize self.count 1#usize
    ok (core.result.Result.Ok (),
      { ac := d1, bd := d2, ad := d3, bc := d4, count := i })

@[simp] private theorem bind_ok_iff {α β : Type} (r : Result α)
    (f : α → Result β) (y : β) :
    Bind.bind r f = .ok y ↔ ∃ x, r = .ok x ∧ f x = .ok y := by
  constructor
  · exact bind_ok_inv r f y
  · rintro ⟨x, rfl, h⟩
    exact h

theorem push_success_state_shape
    (fromWide : Wide → Result (Array Q 2#usize))
    (pushDot : Dot → Q → Q → Result Dot)
    (addUsize : Usize → Usize → Result Usize)
    (self : State) (left right : Wide) (out : State)
    (h : pushWithOps fromWide pushDot addUsize self left right =
      .ok (.Ok (), out)) :
    ∃ leftParts a b rightParts c d dAC dBD dAD dBC i,
      self.count < maxTerms ∧
      fromWide left = .ok leftParts ∧
      Array.index_usize leftParts 0#usize = .ok a ∧
      Array.index_usize leftParts 1#usize = .ok b ∧
      fromWide right = .ok rightParts ∧
      Array.index_usize rightParts 0#usize = .ok c ∧
      Array.index_usize rightParts 1#usize = .ok d ∧
      pushDot self.ac a c = .ok dAC ∧
      pushDot self.bd b d = .ok dBD ∧
      pushDot self.ad a d = .ok dAD ∧
      pushDot self.bc b c = .ok dBC ∧
      addUsize self.count 1#usize = .ok i ∧
      out = { ac := dAC, bd := dBD, ad := dAD, bc := dBC, count := i } := by
  have hbelow : self.count < maxTerms := by
    by_contra hn
    have hg : self.count >= maxTerms := le_of_not_gt hn
    have hguard : pushWithOps fromWide pushDot addUsize self left right =
        .ok (.Err (), self) := by simp [pushWithOps, hg]
    rw [hguard] at h
    cases h
  have hlt : ¬ self.count >= maxTerms := not_le_of_gt hbelow
  simp only [pushWithOps, if_neg hlt, bind_ok_iff] at h
  rcases h with ⟨leftParts, hleft, a, ha, b, hb,
    rightParts, hright, c, hc, d, hd, dAC, hAC, dBD, hBD,
    dAD, hAD, dBC, hBC, i, hi, hout⟩
  exact ⟨leftParts, a, b, rightParts, c, d, dAC, dBD, dAD, dBC, i,
    hbelow, hleft, ha, hb, hright, hc, hd, hAC, hBD, hAD, hBC, hi,
    by simpa using hout.symm⟩

/-- The EbyE four-call schedule, instantiated with the retained concrete Dot
backend, exposes the four exact raw-call results in source order. -/
theorem push_success_four_dot_raw
    (fromWide : Wide → Result (Array Q 2#usize))
    (rawFn : RawFn)
    (addUsize : Usize → Usize → Result Usize)
    (self : State) (left right : Wide) (out : State)
    (h : pushWithOps fromWide (dotViaRawSource rawFn) addUsize self left right =
      .ok (.Ok (), out)) :
    ∃ leftParts rightParts a b c d rawAC rawBD rawAD rawBC i,
      self.count < maxTerms ∧
      fromWide left = .ok leftParts ∧
      Array.index_usize leftParts 0#usize = .ok a ∧
      Array.index_usize leftParts 1#usize = .ok b ∧
      fromWide right = .ok rightParts ∧
      Array.index_usize rightParts 0#usize = .ok c ∧
      Array.index_usize rightParts 1#usize = .ok d ∧
      rawFn a c = .ok rawAC ∧
      rawFn b d = .ok rawBD ∧
      rawFn a d = .ok rawAD ∧
      rawFn b c = .ok rawBC ∧
      out.ac.sums = AspisR1DotPushLocal.Proof.updatedSums self.ac.sums rawAC ∧
      out.bd.sums = AspisR1DotPushLocal.Proof.updatedSums self.bd.sums rawBD ∧
      out.ad.sums = AspisR1DotPushLocal.Proof.updatedSums self.ad.sums rawAD ∧
      out.bc.sums = AspisR1DotPushLocal.Proof.updatedSums self.bc.sums rawBC ∧
      addUsize self.count 1#usize = .ok i ∧
      out.count = i := by
  obtain ⟨leftParts, a, b, rightParts, c, d, dAC, dBD, dAD, dBC, i,
      hbelow, hleft, ha, hb, hright, hc, hd, hAC, hBD, hAD, hBC, hi, hout⟩ :=
    push_success_state_shape fromWide (dotViaRawSource rawFn) addUsize self left right out h
  obtain ⟨rawAC, hrawAC, hstateAC⟩ := dotViaRawSource_success rawFn self.ac a c dAC hAC
  obtain ⟨rawBD, hrawBD, hstateBD⟩ := dotViaRawSource_success rawFn self.bd b d dBD hBD
  obtain ⟨rawAD, hrawAD, hstateAD⟩ := dotViaRawSource_success rawFn self.ad a d dAD hAD
  obtain ⟨rawBC, hrawBC, hstateBC⟩ := dotViaRawSource_success rawFn self.bc b c dBC hBC
  refine ⟨leftParts, rightParts, a, b, c, d, rawAC, rawBD, rawAD, rawBC, i,
    hbelow, hleft, ha, hb, hright, hc, hd, hrawAC, hrawBD, hrawAD, hrawBC,
    ?_, ?_, ?_, ?_, hi, ?_⟩
  · rw [hout]; exact hstateAC
  · rw [hout]; exact hstateBD
  · rw [hout]; exact hstateAD
  · rw [hout]; exact hstateBC
  · rw [hout]

def Bounded (n : Nat) (s : State) : Prop :=
  sumsBelowCount n s.ac.sums ∧ sumsBelowCount n s.bd.sums ∧
    sumsBelowCount n s.ad.sums ∧ sumsBelowCount n s.bc.sums

theorem four_dot_count_range_step
    (n : Nat) (s out : State) (rAC rBD rAD rBC : Array U64 4#usize)
    (hcount : s.count.val = n)
    (hguard : s.count < maxTerms)
    (hinv : Bounded n s)
    (hAC : out.ac.sums = AspisR1DotPushLocal.Proof.updatedSums s.ac.sums rAC)
    (hBD : out.bd.sums = AspisR1DotPushLocal.Proof.updatedSums s.bd.sums rBD)
    (hAD : out.ad.sums = AspisR1DotPushLocal.Proof.updatedSums s.ad.sums rAD)
    (hBC : out.bc.sums = AspisR1DotPushLocal.Proof.updatedSums s.bc.sums rBC)
    (hcount' : out.count.val = n + 1) :
    Bounded (n + 1) out ∧ out.count.val = n + 1 ∧
      (∀ j, ∀ hj : j < 4,
        (s.ac.sums.val[j]'(by rw [s.ac.sums.property]; exact hj)).val < 2^46) ∧
      (∀ j, ∀ hj : j < 4,
        (s.bd.sums.val[j]'(by rw [s.bd.sums.property]; exact hj)).val < 2^46) ∧
      (∀ j, ∀ hj : j < 4,
        (s.ad.sums.val[j]'(by rw [s.ad.sums.property]; exact hj)).val < 2^46) ∧
      (∀ j, ∀ hj : j < 4,
        (s.bc.sums.val[j]'(by rw [s.bc.sums.property]; exact hj)).val < 2^46) := by
  have hguardVal : s.count.val < 4096 := by simpa [maxTerms] using hguard
  have hn : n < 4096 := by rw [← hcount]; exact hguardVal
  have hACpost := updatedSums_below_succ_count n s.ac.sums rAC hn hinv.1
  have hBDpost := updatedSums_below_succ_count n s.bd.sums rBD hn hinv.2.1
  have hADpost := updatedSums_below_succ_count n s.ad.sums rAD hn hinv.2.2.1
  have hBCpost := updatedSums_below_succ_count n s.bc.sums rBC hn hinv.2.2.2
  have hACpre := count_bound_to_preaccumulator n s.ac.sums hn hinv.1
  have hBDpre := count_bound_to_preaccumulator n s.bd.sums hn hinv.2.1
  have hADpre := count_bound_to_preaccumulator n s.ad.sums hn hinv.2.2.1
  have hBCpre := count_bound_to_preaccumulator n s.bc.sums hn hinv.2.2.2
  rw [← hAC] at hACpost
  rw [← hBD] at hBDpost
  rw [← hAD] at hADpost
  rw [← hBC] at hBCpost
  refine ⟨⟨hACpost,hBDpost,hADpost,hBCpost⟩,hcount',?_,?_,?_,?_⟩
  · exact hACpre
  · exact hBDpre
  · exact hADpre
  · exact hBCpre

/-- One successful four-Dot push, with the source checked count addition,
advances all four independent accumulator bounds together. The pre-call
`2^46` bounds are returned for the next raw-step theorem. -/
theorem successful_four_dot_count_bound
    (fromWide : Wide → Result (Array Q 2#usize))
    (rawFn : RawFn)
    (n : Nat) (self out : State) (left right : Wide)
    (hinv : Bounded n self)
    (hcount : self.count.val = n)
    (h : pushWithOps fromWide (dotViaRawSource rawFn) sourceAddUsize self left right =
        .ok (.Ok (), out)) :
    Bounded (n+1) out ∧
      (∀ j, ∀ hj : j < 4,
        (self.ac.sums.val[j]'(by rw [self.ac.sums.property]; exact hj)).val < 2^46) ∧
      (∀ j, ∀ hj : j < 4,
        (self.bd.sums.val[j]'(by rw [self.bd.sums.property]; exact hj)).val < 2^46) ∧
      (∀ j, ∀ hj : j < 4,
        (self.ad.sums.val[j]'(by rw [self.ad.sums.property]; exact hj)).val < 2^46) ∧
      (∀ j, ∀ hj : j < 4,
        (self.bc.sums.val[j]'(by rw [self.bc.sums.property]; exact hj)).val < 2^46) := by
  rcases push_success_four_dot_raw fromWide rawFn sourceAddUsize self left right out h with
    ⟨leftParts, rightParts, a, b, c, d, rawAC, rawBD, rawAD, rawBC, i,
      hbelow, hleft, ha, hb, hright, hc, hd, hrawAC, hrawBD, hrawAD,
      hrawBC, hAC, hBD, hAD, hBC, hi, houtCount⟩
  have hincSpec := UScalar.add_equiv self.count 1#usize
  change (self.count + 1#usize : Result Usize) = .ok i at hi
  rw [hi] at hincSpec
  have houtCountVal : out.count.val = n+1 := by
    calc
      out.count.val = i.val := congrArg (fun x : Usize => x.val) houtCount
      _ = self.count.val + 1 := hincSpec.2.1
      _ = n+1 := by rw [hcount]
  rcases four_dot_count_range_step n self out rawAC rawBD rawAD rawBC
      hcount hbelow hinv hAC hBD hAD hBC houtCountVal with
    ⟨hbounded, _, hacPre, hbdPre, hadPre, hbcPre⟩
  exact ⟨hbounded, hacPre, hbdPre, hadPre, hbcPre⟩

#print axioms push_success_state_shape
#print axioms push_success_four_dot_raw
#print axioms four_dot_count_range_step
#print axioms successful_four_dot_count_bound

end AspisR1EbyEFourDotSourceStepV1
