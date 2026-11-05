import NGQ_EventBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGQ_QueryBudget
open Aeneas Aeneas.Std Result CheckpointBytes5Effect NGQ_EventBounds

theorem bind_bound {A B : Type} {code : Code A} {m n : Nat}
    (bound : Budget code m) (k : A → Code B)
    (each : ∀ a, Budget (k a) n) : Budget (code >>= k) (m+n) := by
  induction bound with
  | done a => exact each a
  | step r c m children ih =>
    exact Budget.step r _ (m+n) (fun b => ih b)
  | read parts c m children ih =>
    have h := Budget.read parts (fun b => bind (c b) k) (m+n) (fun b => ih b)
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem query_bound (B : AspisR1PublicPreparation.QueriesModel.Boundaries)
    (self : AspisR1PublicPreparation.transcript.Transcript Unit)
    (row : U8) (payload : Slice U8) : Budget (NGQ_Effects.code B self row payload) 17 := by
  unfold NGQ_Effects.code
  apply bind_bound (absorb_bound self row payload)
  intro absorbed
  have h := bind_bound (materialize_bound absorbed.state)
    (fun pair => liftResult (NGQ_QueryFactor.finishQuery B NGQ_Effects.dummy absorbed pair.1 pair.2))
    (fun pair => pure_bound _)
  simpa only [Nat.add_zero] using h

/-- Unsuccessful oracle attempts and pure sampler rejection are covered; there
is no ninth-block retry hidden in the query effect model. -/
theorem attempts_at_most17
    (B : AspisR1PublicPreparation.QueriesModel.Boundaries)
    (self : AspisR1PublicPreparation.transcript.Transcript Unit)
    (row : U8) (payload : Slice U8)
    {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest}
    {out : Result NGQ_Effects.Reply} {events : SdkC_Source.Log}
    (trace : NGQ_Cuts.Trace hashv (NGQ_Effects.code B self row payload) out events) :
    events.length≤17 := trace_bound (query_bound B self row payload) trace
#print axioms bind_bound
#print axioms query_bound
#print axioms attempts_at_most17
end AspisR1.NGQ_QueryBudget
end
