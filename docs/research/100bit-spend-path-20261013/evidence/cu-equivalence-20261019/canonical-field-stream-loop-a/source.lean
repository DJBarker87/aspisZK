import AspisR1CanonicalFieldStream.Funs
import CuSavingsCanonicalDotsInvariant
import CuSavingsCanonicalCandidate5
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalFieldStreamLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1CanonicalDots
open CuSavingsCanonicalDotsPush CuSavingsCanonicalDotsField
variable [Shared]
abbrev E := field.wide_exact.WideExact
abbrev K := field.QM31
abbrev Output := core.result.Result E verifier.Error

private theorem bind_ok {A B : Type} (m : Result A) (k : A → Result B) (out : B)
    (h : (m >>= k)=.ok out) : ∃ value,m=.ok value ∧ k value=.ok out := by
  cases m with
  | fail e => cases h
  | div => cases h
  | ok value => exact ⟨value,rfl,h⟩

/-- The actual source checked public push advances the bounded source count.
This also proves finite traversal even for an arbitrary cursor implementation. -/
theorem push_progress (self out : old_pairing.EbyKDot) (value : E) (scalar : K)
    (hc : WideCanonical value)
    (h : old_pairing.EbyKDot.push self value scalar=.ok (.Ok (),out)) :
    self.count.val < 4096 ∧ out.count.val=self.count.val+1 := by
  unfold old_pairing.EbyKDot.push at h
  split at h
  · cases h
  · rename_i hn
    have hb : self.count.val < 4096 := by
      simp only [old_pairing.MAX_TERMS] at hn
      scalar_tac
    simp only [field.wide_exact.WideExact.impl.c0,field.wide_exact.WideExact.impl.c1,
      CuSavingsCanonicalDotsChecked.checked_q value.c0 hc.1,
      CuSavingsCanonicalDotsChecked.checked_q value.c1 hc.2,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch] at h
    cases hs : old_pairing.checked_q scalar with
    | fail e => rw [hs] at h;cases h
    | div => rw [hs] at h;cases h
    | ok check =>
      rw [hs] at h
      cases check with
      | Err e => cases h
      | Ok word =>
        simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at h
        obtain ⟨left,_,h⟩ := bind_ok _ _ _ h
        obtain ⟨right,_,h⟩ := bind_ok _ _ _ h
        obtain ⟨count,hcount,h⟩ := bind_ok _ _ _ h
        have heq := congrArg Prod.snd (Result.ok.inj h)
        cases heq
        obtain ⟨count1,hcount1,hval⟩ := WP.spec_imp_exists
          (UScalar.add_spec (x:=self.count) (y:=1#usize) (by scalar_tac))
        rw [hcount] at hcount1
        cases Result.ok.inj hcount1
        exact ⟨hb,by simpa only [UScalar.ofNatCore_val_eq] using hval⟩

def body {S T : Type} (next : S → Result (Option (E × K) × S))
    (push : T → E → K → Result (core.result.Result Unit Unit × T))
    (finish : T → Result E) (state : S × T) : Result (ControlFlow (S × T) Output) := do
  let (entry,cursor) ← next state.1
  match entry with
  | none => do
    let value ← finish state.2
    .ok (.done (.Ok value))
  | some (value,scalar) => do
    let (result,dot) ← push state.2 value scalar
    match result with
    | .Ok _ => .ok (.cont (cursor,dot))
    | .Err _ => .ok (.done (.Err verifier.Error.Parse))

def oldRun {S : Type} (next : S → Result (Option (E × K) × S))
    (cursor : S) (state : old_pairing.EbyKDot) : Result Output :=
  loop (body next old_pairing.EbyKDot.push old_pairing.EbyKDot.finish) (cursor,state)

def newRun {S : Type} (next : S → Result (Option (E × K) × S))
    (cursor : S) (state : new_pairing.EbyKDot) : Result Output :=
  loop (body next new_pairing.EbyKDot.push new_pairing.EbyKDot.finish) (cursor,state)

private theorem unroll {S T : Type} (b : S → Result (ControlFlow S T)) (s : S) :
    loop b s = (do let flow ← b s
                   match flow with
                   | .done v => .ok v
                   | .cont t => loop b t) := by
  rw [loop]
  cases b s with
  | fail e => rfl
  | div => rfl
  | ok flow => cases flow <;> rfl

/-- Full computational equality, including parser/index failure, source errors
and divergence. Canonicality is required only for successful actual reads.
The original 4096-term guard bounds every successful continuation. -/
theorem run_equivalence {S : Type} (next : S → Result (Option (E × K) × S))
    (canonical : ∀ cursor value scalar cursor1,
      next cursor=.ok (some (value,scalar),cursor1) → WideCanonical value)
    (cursor : S) (state : old_pairing.EbyKDot) (hc : RelatedCounts state) :
    newRun next cursor (project state)=oldRun next cursor state := by
  generalize hrank : 4097-state.count.val=rank
  induction rank using Nat.strong_induction_on generalizing cursor state with
  | h rank ih =>
    unfold newRun oldRun
    rw [unroll,unroll]
    unfold body
    dsimp only
    cases hn : next cursor with
    | fail e => rfl
    | div => rfl
    | ok entry =>
      rcases entry with ⟨entry,cursor1⟩
      cases entry with
      | none =>
        rw [CuSavingsCanonicalCandidate5.finalization]
      | some pair =>
        rcases pair with ⟨value,scalar⟩
        have hv := canonical cursor value scalar cursor1 hn
        rw [public_push state value scalar hv hc]
        simp only [bind_assoc_eq,bind_tc_ok]
        cases hp : old_pairing.EbyKDot.push state value scalar with
        | fail e => rfl
        | div => rfl
        | ok entry =>
          rcases entry with ⟨result,state1⟩
          cases result with
          | Err e => rfl
          | Ok unit =>
            cases unit
            have hpcount := push_progress state state1 value scalar hv hp
            have hcounts := CuSavingsCanonicalDotsInvariant.push_counts state state1 value scalar hv hc hp
            have hlt : 4097-state1.count.val < rank := by omega
            exact ih _ hlt cursor1 state1 hcounts rfl

#print axioms push_progress
#print axioms run_equivalence
end AspisR1.CuSavingsCanonicalFieldStreamLoop
