import R1Z.ProverRwRetryModel
import PV_DIAG2_Effects

/-! Effect instrumentation of the actual retry model. Every attempt supplies
its complete effects, including failures; no source-silence fact is assumed.
Erasure is a theorem about the Result projection, not the observer. -/
set_option autoImplicit false
namespace PV_DIAG2
open Aeneas Aeneas.Std Result
open R1Z ProverCommitRetry34 ProverCommitSemanticTransport26

structure Observed (A : Type) where
 effects : List Effect
 result : Result A

def eraseAttempt {S P : Type} (a : Nat → S → Observed (Step P × S)) : Attempt S P :=
 fun k s => (a k s).result

def runEffects {S P : Type} (a : Nat → S → Observed (Step P × S)) :
 Nat → Nat → S → Observed (Step (Published P) × S)
 | 0, _, s => ⟨[], ok (.stop .AttemptsExhausted,s)⟩
 | n+1, k, s =>
   let first := a k s
   match first.result with
   | .fail e => ⟨.entered k :: first.effects, .fail e⟩
   | .div => ⟨.entered k :: first.effects, .div⟩
   | .ok (.done p,after) => ⟨.entered k :: first.effects, ok (.done ⟨p,k+1⟩,after)⟩
   | .ok (.stop e,after) => ⟨.entered k :: first.effects, ok (.stop e,after)⟩
   | .ok (.retry,after) =>
     let rest := runEffects a n (k+1) after
     ⟨.entered k :: (first.effects ++ (.rejected k :: rest.effects)), rest.result⟩

theorem erase_run {S P : Type} (a : Nat → S → Observed (Step P × S))
    (n k : Nat) (s : S) :
 (runEffects a n k s).result = run (eraseAttempt a) n k s := by
 induction n generalizing k s with
 | zero => rfl
 | succ n ih =>
   simp only [runEffects,run,eraseAttempt]
   cases h : (a k s).result with
   | fail e => rfl
   | div => rfl
   | ok pair =>
     rcases pair with ⟨step,after⟩
     cases step with
     | done p => rfl
     | stop e => rfl
     | retry => exact ih (k+1) after

/-- No retry effect is erased, even if the continuation subsequently fails. -/
theorem rejected_effects {S P : Type} (a : Nat → S → Observed (Step P × S))
    (n k : Nat) (s after : S) (h : (a k s).result = ok (.retry,after)) :
 runEffects a (n+1) k s =
 ⟨.entered k :: ((a k s).effects ++ (.rejected k :: (runEffects a n (k+1) after).effects)),
   (runEffects a n (k+1) after).result⟩ := by
 simp only [runEffects,h]

/-- The controller itself adds no stderr, log, capture, panic or OOM effect
when it reaches the cap. Its caller still reports AttemptsExhausted. -/
theorem cap_no_direct_effects {S P : Type} (a : Nat → S → Observed (Step P × S))
    (k : Nat) (s : S) : (runEffects a 0 k s).effects = [] := rfl

theorem fatal_effects_retained {S P : Type} (a : Nat → S → Observed (Step P × S))
    (n k : Nat) (s : S) (e : Aeneas.Std.Error) (h : (a k s).result = .fail e) :
 (runEffects a (n+1) k s).effects = .entered k :: (a k s).effects := by
 simp only [runEffects,h]

/-- Install the emitted per-attempt Result law without any hypothesis that
its diagnostic effects vanish or that frames are public. Those remain P. -/
theorem source_retry_result [ProverRwFull.ExternalTypes] [ProverRwFull.ExternalFuns]
    {C : Type} (entropy : ProverRwRetryModel.Entropy C)
    (pub : ProverRwRetryModel.Pub) (compiled : ProverRwRetryModel.Compiled)
    (variant : ProverRwFull.transport.Variant) (hash : ProverRwRetryModel.Hash)
    (store : ProverRwRetryModel.Store) (callback : C) (k : Usize) (n : Nat)
    (bound : k.val+n=8)
    (a : Nat → (C × ProverRwRetryModel.Store) →
      Observed (Step ProverRwRetryModel.Proof × (C × ProverRwRetryModel.Store)))
    (resultLaw : ∀ i s, (a i s).result =
      ProverRwRetryModel.attempt entropy pub compiled variant hash i s) :
 mapR ProverRwRetryModel.drop (runEffects a n k.val (callback,store)).result =
 mapR ProverRwRetryModel.sourceOutput
   (ProverRwFull.prover.retry_attempt entropy pub compiled variant hash store callback k) := by
 rw [erase_run]
 rw [run_congr (eraseAttempt a) (ProverRwRetryModel.attempt entropy pub compiled variant hash)
   resultLaw n k.val (callback,store)]
 exact (ProverRwRetryModel.retry entropy pub compiled variant hash store callback k n bound).symm

theorem mask_exhaustion_rejected :
 ProverRwFull.prover.mask_error
   ProverRwFull.aspis_prover.state_only_hiding.StateOnlyMaskBuildError.MaskSampleExhausted =
 ok ProverRwFull.verifier.Error.Rejected := by
 simp [ProverRwFull.prover.mask_error,
  ProverRwFull.aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Insts.CoreCmpPartialEqStateOnlyMaskBuildError.eq]

#print axioms erase_run
#print axioms rejected_effects
#print axioms cap_no_direct_effects
#print axioms fatal_effects_retained
#print axioms source_retry_result
#print axioms mask_exhaustion_rejected
end PV_DIAG2
