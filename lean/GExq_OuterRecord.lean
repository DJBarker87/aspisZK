import GExq_OuterLower
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_OuterRecord
open Aeneas Aeneas.Std Result GExq_OuterLower

inductive Event where
  | first (semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
      (pub proof : Slice U8) (split : Usize)
      (answer : core.result.Result (alloc.vec.Vec U8) AdapterRw.aspis_r1_cost_probe.verifier.Error)
  | second (pub proof checkpoint : Slice U8)
      (answer : core.result.Result Unit AdapterRw.aspis_r1_cost_probe.verifier.Error)

def project {A : Type} : S2W_Trace.Call A → A → List Event
  | .op10 _ semantic pub proof split _ _, answer => [.first semantic pub proof split answer]
  | .op11 _ pub proof checkpoint _ _, answer => [.second pub proof checkpoint answer]
  | _, _ => []

def record (impl : {A : Type} → S2W_Trace.Call A → Oracle A) {A : Type} :
    Native A → List Event → Oracle (A × List Event)
  | .done a, before => .done (a,before)
  | .step r k, before => .step r (fun a => record impl (k a) before)
  | .call op k, before => CheckpointBytes5Effect.bind (impl op)
      (fun a => record impl (k a) (before ++ project op a))

theorem erase_record {A : Type} (sdk : AdapterRw.Ops)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (impl : {B : Type} → S2W_Trace.Call B → Oracle B)
    (law : ∀ {B : Type} (call : S2W_Trace.Call B), GExq_ChildCode.Admissible hashv call →
      CheckpointBytes5Effect.erase (SdkC_Source.dictionary hashv) () (impl call) = S2W_Trace.invoke sdk call)
    (code : Native A) (good : Good hashv code) (before : List Event) :
    (CheckpointBytes5Effect.erase (SdkC_Source.dictionary hashv) () (record impl code before) >>=
      fun pair => ok pair.1) = S2W_Trace.erase sdk code := by
  induction code generalizing before with
  | done a => rfl
  | step r k ih =>
    cases r with
    | fail e => rfl
    | div => rfl
    | ok a => exact ih a good before
  | call op k ih =>
    simp only [record,GExq_OuterLower.erase_bind_explicit,law op good.1,S2W_Trace.erase]
    cases S2W_Trace.invoke sdk op with
    | fail e => rfl
    | div => rfl
    | ok a => exact ih a (good.2 a) (before ++ project op a)

#print axioms erase_record
end AspisR1.GExq_OuterRecord
end
