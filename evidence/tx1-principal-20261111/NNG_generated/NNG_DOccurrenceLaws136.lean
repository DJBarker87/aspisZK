import NNG_DEnvObserved136
import NNG_SourceStep136
import NNG_Standard136
import NNG_FromFnValues136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DOccurrenceLaws136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Array136 NNG_SourceStep136

/-- Source-ordered local graph clauses at entered calls of ONE trace and ONE
Env. The original semantic Prefix remains a.prefix_. All clauses must be
DISCHARGED from CLOSED children at their actual arguments in a candidate;
this packet is not a permitted remaining root hypothesis. -/
structure Laws (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (env : RSL.Env) {A : Type} (whole : Code A) : Prop where
  inputs : Inputs VL p a s
  fromFn : (@Calls.c0 c) = @NNG_StdArray.implementation
  mapErr : (@Calls.c1 c) = @NNG_StdMapErr.run
  pointEq : c.c2 = NNG_Equality136.pointEq
  qeq : c.c3 = NNG_Equality136.qeq
  mark : ∀ (site : String) (obs : NNG_Emitted.Observer) (i : U8),
    NMT_CallTree.Event.call site (obs,i) (c.c9 obs i) ∈ (run whole).2 →
    RSL.Spec.map id (NNG_Interpret136.call events site (obs,i) (c.c9 obs i)) env =
      (RSL.Spec.pure ()) env
  rounds : 
    NMT_CallTree.Event.call "rounds" (s.prefixValue,s.transcript) (c.c10 s.digest s.prefixValue s.transcript) ∈ (run whole).2 →
    RSL.Spec.map (NNG_DProjection136.rounds p) (NNG_Interpret136.call events "rounds" (s.prefixValue,s.transcript) (c.c10 s.digest s.prefixValue s.transcript)) env =
      (VL.semanticRounds.run (a.prefix_,a.transcript)) env
  claims : 
    NMT_CallTree.Event.call "claims" s.prefixValue (c.c8 s.prefixValue) ∈ (run whole).2 →
    RSL.Spec.map (claimsReply p) (NNG_Interpret136.call events "claims" s.prefixValue (c.c8 s.prefixValue)) env =
      (VL.claims.run a.prefix_) env
  terminal : ∀ (claims : Claims) (alpha : Alpha),
    NMT_CallTree.Event.call "terminal" (s.publicValue,claims,alpha,s.challenges) (c.c7 s.publicValue claims alpha s.challenges) ∈ (run whole).2 →
    RSL.Spec.map (terminalReply p) (NNG_Interpret136.call events "terminal" (s.publicValue,claims,alpha,s.challenges) (c.c7 s.publicValue claims alpha s.challenges)) env =
      (VL.terminalQm31.run (a.public_,p.claims claims,p.alpha alpha,VL.origChallenges a.challenges)) env
  mask : ∀ (claims : Claims) (alpha : Alpha),
    NMT_CallTree.Event.call "mask" (NNG_FromFnValues136.low claims,NNG_FromFnValues136.high claims,cell claims 27#usize (by decide),alpha) (c.c6 (NNG_FromFnValues136.low claims) (NNG_FromFnValues136.high claims) (cell claims 27#usize (by decide)) alpha) ∈ (run whole).2 →
    RSL.Spec.map (p.q) (NNG_Interpret136.call events "mask" (NNG_FromFnValues136.low claims,NNG_FromFnValues136.high claims,cell claims 27#usize (by decide),alpha) (c.c6 (NNG_FromFnValues136.low claims) (NNG_FromFnValues136.high claims) (cell claims 27#usize (by decide)) alpha)) env =
      (RSL.Spec.pure (VL.maskValue (p.claims claims) (p.alpha alpha))) env
  record25 : 
    NMT_CallTree.Event.call "record25" (s.prefixValue,25#u8) (c.c11 s.prefixValue 25#u8) ∈ (run whole).2 →
    RSL.Spec.map (recordReply p) (NNG_Interpret136.call events "record25" (s.prefixValue,25#u8) (c.c11 s.prefixValue 25#u8)) env =
      (RSL.RE.ofExcept (VL.validatedRecord a.prefix_ 25)) env
  extra : ∀ (rec : r1_wire.ValidatedRecord),
    NMT_CallTree.Event.call "extra" (rec,87#usize) (c.c15 29#usize rec 87#usize) ∈ (run whole).2 →
    RSL.Spec.map (decodeReply p) (NNG_Interpret136.call events "extra" (rec,87#usize) (c.c15 29#usize rec 87#usize)) env =
      (RSL.RE.ofExcept (VL.decodeK29 (p.record rec) 87)) env
  multiply : ∀ (x y : Q),
    NMT_CallTree.Event.call "multiply" (x,y) (c.c5 x y) ∈ (run whole).2 →
    RSL.Spec.map (p.q) (NNG_Interpret136.call events "multiply" (x,y) (c.c5 x y)) env =
      (RSL.Spec.pure (VL.qmul (p.q x) (p.q y))) env
  addMask : ∀ (x y : Q),
    NMT_CallTree.Event.call "addMask" (x,y) (c.c4 x y) ∈ (run whole).2 →
    RSL.Spec.map (p.q) (NNG_Interpret136.call events "addMask" (x,y) (c.c4 x y)) env =
      (RSL.Spec.pure (VL.qadd (p.q x) (p.q y))) env
  addExtra : ∀ (x y : Q),
    NMT_CallTree.Event.call "addExtra" (x,y) (c.c4 x y) ∈ (run whole).2 →
    RSL.Spec.map (p.q) (NNG_Interpret136.call events "addExtra" (x,y) (c.c4 x y)) env =
      (RSL.Spec.pure (VL.qadd (p.q x) (p.q y))) env
  state : ∀ (t : r1_wire.SemanticTranscript H),
    NMT_CallTree.Event.call "state" t (c.c14 s.digest t) ∈ (run whole).2 →
    RSL.Spec.map (p.b32) (NNG_Interpret136.call events "state" t (c.c14 s.digest t)) env =
      (RSL.Spec.pure (VL.state (p.transcript t))) env
  circle0 : ∀ (t : r1_wire.SemanticTranscript H) (rec : r1_wire.ValidatedRecord),
    NMT_CallTree.Event.call "circle0" (t,rec) (c.c13 s.digest t rec) ∈ (run whole).2 →
    RSL.Spec.map (circleReply p) (NNG_Interpret136.call events "circle0" (t,rec) (c.c13 s.digest t rec)) env =
      (VL.circle.run (p.transcript t,p.record rec)) env
  record26 : 
    NMT_CallTree.Event.call "record26" (s.prefixValue,26#u8) (c.c11 s.prefixValue 26#u8) ∈ (run whole).2 →
    RSL.Spec.map (recordReply p) (NNG_Interpret136.call events "record26" (s.prefixValue,26#u8) (c.c11 s.prefixValue 26#u8)) env =
      (RSL.RE.ofExcept (VL.validatedRecord a.prefix_ 26)) env
  beforeZ1 : ∀ (rec : r1_wire.ValidatedRecord),
    NMT_CallTree.Event.call "beforeZ1" (rec,0#usize) (c.c15 29#usize rec 0#usize) ∈ (run whole).2 →
    RSL.Spec.map (decodeReply p) (NNG_Interpret136.call events "beforeZ1" (rec,0#usize) (c.c15 29#usize rec 0#usize)) env =
      (RSL.RE.ofExcept (VL.decodeK29 (p.record rec) 0)) env
  circle1 : ∀ (t : r1_wire.SemanticTranscript H) (rec : r1_wire.ValidatedRecord),
    NMT_CallTree.Event.call "circle1" (t,rec) (c.c13 s.digest t rec) ∈ (run whole).2 →
    RSL.Spec.map (circleReply p) (NNG_Interpret136.call events "circle1" (t,rec) (c.c13 s.digest t rec)) env =
      (VL.circle.run (p.transcript t,p.record rec)) env
  payload2 : 
    NMT_CallTree.Event.call "payload2" (s.prefixValue,2#u8) (c.c12 s.prefixValue 2#u8) ∈ (run whole).2 →
    RSL.Spec.map (payloadReply p) (NNG_Interpret136.call events "payload2" (s.prefixValue,2#u8) (c.c12 s.prefixValue 2#u8)) env =
      (RSL.RE.ofExcept (VL.payload a.prefix_ 2)) env
  roundsCanonical :
    NMT_CallTree.Event.call "rounds" (s.prefixValue,s.transcript)
      (c.c10 s.digest s.prefixValue s.transcript) ∈ (run whole).2 →
    ∀ (running : Q) (alpha : Alpha) (t1 : r1_wire.SemanticTranscript H),
      c.c10 s.digest s.prefixValue s.transcript = .ok (.Ok (running,alpha,t1)) → p.qDom running
  addExtraCanonical : ∀ (x y : Q),
    NMT_CallTree.Event.call "addExtra" (x,y) (c.c4 x y) ∈ (run whole).2 →
    ∀ z, c.c4 x y = .ok z → p.qDom z

/-- Restrict only along a proved SAME-trace inclusion. Returned canonicality
is a callee-derived local invariant, not an added own-input clause. -/
theorem restrict (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W A B : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (whole : Code A) (part : Code B) (h : Laws VL a p c s events env whole)
    (within : Within part whole) : Laws VL a p c s events env part := by
  refine ⟨h.inputs,h.fromFn,h.mapErr,h.pointEq,h.qeq,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro site obs i entered
    exact h.mark site obs i (within _ entered)
  · intro entered
    exact h.rounds (within _ entered)
  · intro entered
    exact h.claims (within _ entered)
  · intro claims alpha entered
    exact h.terminal claims alpha (within _ entered)
  · intro claims alpha entered
    exact h.mask claims alpha (within _ entered)
  · intro entered
    exact h.record25 (within _ entered)
  · intro rec entered
    exact h.extra rec (within _ entered)
  · intro x y entered
    exact h.multiply x y (within _ entered)
  · intro x y entered
    exact h.addMask x y (within _ entered)
  · intro x y entered
    exact h.addExtra x y (within _ entered)
  · intro t entered
    exact h.state t (within _ entered)
  · intro t rec entered
    exact h.circle0 t rec (within _ entered)
  · intro entered
    exact h.record26 (within _ entered)
  · intro rec entered
    exact h.beforeZ1 rec (within _ entered)
  · intro t rec entered
    exact h.circle1 t rec (within _ entered)
  · intro entered
    exact h.payload2 (within _ entered)
  · intro entered running alpha t1 returned
    exact h.roundsCanonical (within _ entered) running alpha t1 returned
  · intro x y entered z returned
    exact h.addExtraCanonical x y (within _ entered) z returned
#print axioms restrict
end AspisR1.NNG_DOccurrenceLaws136
