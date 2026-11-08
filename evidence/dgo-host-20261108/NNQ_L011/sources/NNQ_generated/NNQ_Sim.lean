import NNQ_Observe
import GExq_OuterLower
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNQ_HostDigest
open Aeneas Aeneas.Std Result AdapterRw S2W_Trace

def NotDigest {B : Type} (c : Call B) : Prop := S2W_Trace.operationId c ≠ 43

inductive CallSim : {B : Type} → Call B → Call B → Prop where
  | same {B : Type} (c : Call B) (h : NotDigest c) : CallSim c c
  | op10 {H : Type} (D1 D2 : aspis_core.digest.Digest32 H)
      (hc : D1.coremarkerCopyInst = D2.coremarkerCopyInst)
      (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
      (pub proof : Slice U8) (split : Usize) (hash : H)
      (obs : Option (aspis_r1_cost_probe.verifier.Phase → Result Unit)) :
      CallSim (.op10 D1 semantic pub proof split hash obs) (.op10 D2 semantic pub proof split hash obs)
  | op11 {H : Type} (D1 D2 : aspis_core.digest.Digest32 H)
      (hc : D1.coremarkerCopyInst = D2.coremarkerCopyInst)
      (pub proof ck : Slice U8) (hash : H)
      (obs : Option (aspis_r1_cost_probe.verifier.Phase → Result Unit)) :
      CallSim (.op11 D1 pub proof ck hash obs) (.op11 D2 pub proof ck hash obs)
inductive Sim {A : Type} : Code A → Code A → Prop where
  | done (a : A) : Sim (.done a) (.done a)
  | step {B : Type} (r : Result B) (k1 k2 : B → Code A) (hk : ∀ b, Sim (k1 b) (k2 b)) :
      Sim (.step r k1) (.step r k2)
  | call {B : Type} (c1 c2 : Call B) (k1 k2 : B → Code A) (hc : CallSim c1 c2)
      (hk : ∀ b, Sim (k1 b) (k2 b)) : Sim (.call c1 k1) (.call c2 k2)

theorem sim_bind {A B : Type} {p q : Code A} {f g : A → Code B} (h : Sim p q)
    (hk : ∀ a, Sim (f a) (g a)) : Sim (p >>= f) (q >>= g) := by
  induction h with
  | done a => exact hk a
  | step r k1 k2 _ ih => exact .step r _ _ (fun b => ih b)
  | call c1 c2 k1 k2 hc _ ih => exact .call c1 c2 _ _ hc (fun b => ih b)

theorem sim_pure {A : Type} (a : A) : Sim (pure a : Code A) (pure a) := .done a

theorem sim_lift {A : Type} (r : Result A) : Sim (S2W_Trace.liftResult r) (S2W_Trace.liftResult r) :=
  .step r _ _ (fun b => .done b)

theorem sim_perform {A : Type} {c1 c2 : Call A} (h : CallSim c1 c2) :
    Sim (S2W_Trace.perform c1) (S2W_Trace.perform c2) :=
  .call c1 c2 _ _ h (fun b => .done b)

theorem lowerN_sim {A : Type} (impl1 impl2 : {B : Type} → Call B → CheckpointBytes5Effect.Code B)
    (himpl : ∀ {B : Type} (x y : Call B), CallSim x y → impl1 x = impl2 y)
    {c1 c2 : Code A} (h : Sim c1 c2) : GExq_OuterLower.lower impl1 c1 = GExq_OuterLower.lower impl2 c2 := by
  induction h with
  | done a => rfl
  | step r k1 k2 _ ih =>
    simp only [GExq_OuterLower.lower]
    congr 1
    funext b
    exact ih b
  | call c1 c2 k1 k2 hc _ ih =>
    simp only [GExq_OuterLower.lower]
    rw [himpl c1 c2 hc]
    congr 1
    funext b
    exact ih b


#print axioms sim_bind
#print axioms sim_pure
#print axioms sim_lift
#print axioms sim_perform
#print axioms lowerN_sim
end AspisR1.NNQ_HostDigest
end
