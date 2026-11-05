import NGQ_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGQ_EventBounds
open Aeneas Aeneas.Std Result CheckpointBytes5Effect

/-- Static read budget for literal effect syntax; pure rejection/failure may
truncate execution. No freshness or independence is assumed. -/
inductive Budget {A : Type} : Code A → Nat → Prop where
 | done (a : A) : Budget (.done a) 0
 | step {B : Type} (r : Result B) (k : B → Code A) (n : Nat)
     (each : ∀ b, Budget (k b) n) : Budget (.step r k) n
 | read (parts : Parts) (k : Digest → Code A) (n : Nat)
     (each : ∀ d, Budget (k d) n) : Budget (.read parts k) (n+1)

theorem pure_bound {A : Type} (r : Result A) : Budget (liftResult r) 0 :=
  .step r _ 0 (fun a => .done a)

theorem trace_bound {A : Type} {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest}
    {code : Code A} {n : Nat} (bound : Budget code n)
    {out : Result A} {events : SdkC_Source.Log}
    (trace : NGQ_Cuts.Trace hashv code out events) : events.length≤n := by
  induction bound generalizing out events with
  | done a => cases trace; exact Nat.le_refl 0
  | step r k n each ih =>
    cases trace with
    | stepOk r k b edge out events tail => exact ih b tail
    | stepFail r k error edge => exact Nat.zero_le n
    | stepDiv r k edge => exact Nat.zero_le n
  | read parts k n each ih =>
    cases trace with
    | readOk parts k reply edge out events tail =>
      have h := ih reply tail
      simpa only [List.length_cons] using Nat.succ_le_succ h
    | readFail parts k error edge => exact Nat.succ_le_succ (Nat.zero_le n)
    | readDiv parts k edge => exact Nat.succ_le_succ (Nat.zero_le n)

theorem absorb_bound (self : AspisR1PublicPreparation.transcript.Transcript Unit)
    (row : U8) (payload : Slice U8) : Budget (NGQ_Effects.absorbCode self row payload) 1 := by
  unfold NGQ_Effects.absorbCode
  repeat' first
    | (apply Budget.step; intro v; dsimp! only)
    | (apply Budget.read; intro d; dsimp! only)
    | exact Budget.done _

theorem materialize_bound (state : NGQ_Effects.Bytes32) :
    Budget (NGQ_Effects.materializeCode state) 16 := by
  unfold NGQ_Effects.materializeCode
  repeat' first
    | (apply Budget.step; intro v; dsimp! only)
    | (apply Budget.read; intro d; dsimp! only)
    | exact Budget.done _

#print axioms pure_bound
#print axioms trace_bound
#print axioms absorb_bound
#print axioms materialize_bound
end AspisR1.NGQ_EventBounds
end
