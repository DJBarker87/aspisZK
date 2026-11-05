import NHK_EventChain
import NGQ_Concrete
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHK_EffectJoin
open Aeneas Aeneas.Std Result CheckpointBytes5Effect AspisR1PublicPreparation
abbrev Trace := NGQ_Cuts.Trace

theorem normalize_bind {A B : Type} (code : Code A) (k : A → Code B) :
    NGQ_Normalize.normalize (CheckpointBytes5Effect.bind code k) =
      CheckpointBytes5Effect.bind (NGQ_Normalize.normalize code)
        (fun a => NGQ_Normalize.normalize (k a)) := by
  induction code with
  | done a => rfl
  | step r c ih => cases r <;> simp only [CheckpointBytes5Effect.bind,NGQ_Normalize.normalize,ih]
  | read parts c ih => simp only [CheckpointBytes5Effect.bind,NGQ_Normalize.normalize,ih]

theorem normalized_append {A B : Type}
    {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest}
    {code : Code A} {out : Result A} {events : SdkC_Source.Log}
    (trace : Trace hashv (NGQ_Normalize.normalize code) out events)
    (k : A → Code B) (final : Result B) (suffix : SdkC_Source.Log)
    (tail : NHK_TraceBind.Continuation hashv out
      (fun a => NGQ_Normalize.normalize (k a)) final suffix) :
    Trace hashv (NGQ_Normalize.normalize (CheckpointBytes5Effect.bind code k))
      final (events ++ suffix) := by
  rw [normalize_bind]
  exact NHK_TraceBind.append trace _ final suffix tail

theorem pure_trace {A : Type}
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (r : Result A) :
    Trace hashv (NGQ_Normalize.normalize (liftResult r)) r [] := by
  cases r with
  | ok a => exact .done a
  | fail error => exact .stepFail _ _ error rfl
  | div => exact .stepDiv _ _ rfl

/-- A local pure tail observation. Failure/divergence of an earlier digest
has no tail invocation. This is NOT a whole queries Result/log equality. -/
def TailEdge (B : QueriesModel.Boundaries) (absorbed : transcript.Transcript Unit)
    (pairs : Result (NGQ_Effects.Blocks × NGQ_Effects.Blocks))
    (out : Result NGQ_Effects.Reply) : Prop :=
  match pairs with
  | .ok v => NGQ_QueryFactor.finishQuery B NGQ_Effects.dummy absorbed v.1 v.2 = out
  | .fail error => out = .fail error
  | .div => out = .div

def afterAbsorb (B : QueriesModel.Boundaries) (absorbed : transcript.Transcript Unit) : Code NGQ_Effects.Reply := do
  let (blocks,advances) ← NGQ_Effects.materializeCode absorbed.state
  liftResult (NGQ_QueryFactor.finishQuery B NGQ_Effects.dummy absorbed blocks advances)

theorem afterAbsorb_eq (B : QueriesModel.Boundaries) (absorbed : transcript.Transcript Unit) :
    afterAbsorb B absorbed = CheckpointBytes5Effect.bind (NGQ_Effects.materializeCode absorbed.state)
      (fun v => liftResult (NGQ_QueryFactor.finishQuery B NGQ_Effects.dummy absorbed v.1 v.2)) := by
  unfold afterAbsorb
  congr 1
  funext v
  cases v
  rfl

theorem code_shape (B : QueriesModel.Boundaries) (self : transcript.Transcript Unit)
    (row : U8) (payload : Slice U8) :
    NGQ_Effects.code B self row payload =
      CheckpointBytes5Effect.bind (NGQ_Effects.absorbCode self row payload) (afterAbsorb B) := by rfl

/-- Assemble the SAME absorb receiver, eight eagerly materialized pairs and
pure tail. All input cuts are local; no whole-query association is a premise. -/
theorem returning_absorb
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (B : QueriesModel.Boundaries) (self absorbed : transcript.Transcript Unit)
    (row : U8) (payload : Slice U8)
    (absorbEvents pairEvents : SdkC_Source.Log)
    (pairs : Result (NGQ_Effects.Blocks × NGQ_Effects.Blocks))
    (out : Result NGQ_Effects.Reply)
    (absorbCuts : Trace hashv (NGQ_Normalize.normalize (NGQ_Effects.absorbCode self row payload))
      (.ok absorbed) absorbEvents)
    (pairCuts : NHK_EventChain.PartialObservations hashv
      [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize]
      (Array.repeat 8#usize (Array.repeat 32#usize 0#u8))
      (Array.repeat 8#usize (Array.repeat 32#usize 0#u8))
      absorbed.state pairs pairEvents)
    (tailEdge : TailEdge B absorbed pairs out) :
    Trace hashv (NGQ_Normalize.normalize (NGQ_Effects.code B self row payload))
      out (absorbEvents ++ pairEvents) := by
  rw [code_shape]
  apply normalized_append absorbCuts (afterAbsorb B) out pairEvents
  change Trace hashv (NGQ_Normalize.normalize (afterAbsorb B absorbed)) out pairEvents
  rw [afterAbsorb_eq]
  have materializer := NHK_EventChain.eight_partial absorbed.state pairs pairEvents pairCuts
  cases pairs with
  | ok v =>
    rcases v with ⟨blocks,advances⟩
    change NGQ_QueryFactor.finishQuery B NGQ_Effects.dummy absorbed blocks advances = out at tailEdge
    subst out
    exact (by simpa only [List.append_nil] using
      normalized_append materializer
        (fun v => liftResult (NGQ_QueryFactor.finishQuery B NGQ_Effects.dummy absorbed v.1 v.2))
        (NGQ_QueryFactor.finishQuery B NGQ_Effects.dummy absorbed blocks advances) []
        (pure_trace hashv (NGQ_QueryFactor.finishQuery B NGQ_Effects.dummy absorbed blocks advances)))
  | fail error =>
    change out = .fail error at tailEdge
    subst out
    exact (by simpa only [List.append_nil] using
      normalized_append materializer
        (fun v => liftResult (NGQ_QueryFactor.finishQuery B NGQ_Effects.dummy absorbed v.1 v.2)) (.fail error) [] ⟨rfl,rfl⟩)
  | div =>
    change out = .div at tailEdge
    subst out
    exact (by simpa only [List.append_nil] using
      normalized_append materializer
        (fun v => liftResult (NGQ_QueryFactor.finishQuery B NGQ_Effects.dummy absorbed v.1 v.2)) .div [] ⟨rfl,rfl⟩)

theorem absorb_fail
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (B : QueriesModel.Boundaries) (self : transcript.Transcript Unit)
    (row : U8) (payload : Slice U8) (events : SdkC_Source.Log) (error : Error)
    (cuts : Trace hashv (NGQ_Normalize.normalize (NGQ_Effects.absorbCode self row payload))
      (.fail error) events) :
    Trace hashv (NGQ_Normalize.normalize (NGQ_Effects.code B self row payload))
      (.fail error) events := by
  rw [code_shape]
  simpa only [List.append_nil] using
    normalized_append cuts (afterAbsorb B) (.fail error) [] ⟨rfl,rfl⟩

theorem absorb_div
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (B : QueriesModel.Boundaries) (self : transcript.Transcript Unit)
    (row : U8) (payload : Slice U8) (events : SdkC_Source.Log)
    (cuts : Trace hashv (NGQ_Normalize.normalize (NGQ_Effects.absorbCode self row payload))
      .div events) :
    Trace hashv (NGQ_Normalize.normalize (NGQ_Effects.code B self row payload)) .div events := by
  rw [code_shape]
  simpa only [List.append_nil] using
    normalized_append cuts (afterAbsorb B) .div [] ⟨rfl,rfl⟩

#print axioms afterAbsorb_eq
#print axioms code_shape
#print axioms normalize_bind
#print axioms normalized_append
#print axioms pure_trace
#print axioms returning_absorb
#print axioms absorb_fail
#print axioms absorb_div
end AspisR1.NHK_EffectJoin
end
