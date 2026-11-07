import NNG_EnvObserved136
import NNG_SourceStep136
import NNG_Standard136
import NNG_FromFnValues136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_OccurrenceLaws136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_Projection136 NNG_Array136 NNG_SourceStep136

/-- A packet of local SAME-call graph equalities, conditioned on actual entry
in ONE source trace at ONE Env. It contains no parent result, output, success,
post-state or endpoint equality. A final candidate must derive this packet
from CLOSED children and their domains; taking it as a root premise earns no
row credit. No VLib field instance is defined here. -/
structure Laws (VL : RSL.VLib) {H W : Type} (p : Representation VL H)
    (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (env : RSL.Env) {A : Type} (whole : Code A) : Prop where
  fromFn : c.c0 = NNG_StdArray.implementation
  mapErr : c.c1 = NNG_StdMapErr.run
  pointEq : c.c2 = NNG_Equality136.pointEq
  qeq : c.c3 = NNG_Equality136.qeq
  mark : ∀ (site : String) (obs : NNG_Emitted.Observer) (i : U8),
    NMT_CallTree.Event.call site (obs,i) (c.c9 obs i) ∈ (run whole).2 →
    RSL.Spec.map id (NNG_Interpret136.call events site (obs,i) (c.c9 obs i)) env =
      (RSL.Spec.pure ()) env
  rounds : ∀ (pfx : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H),
    NMT_CallTree.Event.call "rounds" (pfx,t) (c.c10 s.digest pfx t) ∈ (run whole).2 →
    RSL.Spec.map (NNG_Projection136.rounds p) (NNG_Interpret136.call events "rounds" (pfx,t) (c.c10 s.digest pfx t)) env =
      (VL.semanticRounds.run (p.prefixValue pfx,p.transcript t)) env
  claims : ∀ (pfx : r1_wire.Prefix),
    NMT_CallTree.Event.call "claims" pfx (c.c8 pfx) ∈ (run whole).2 →
    RSL.Spec.map (claimsReply p) (NNG_Interpret136.call events "claims" pfx (c.c8 pfx)) env =
      (VL.claims.run (p.prefixValue pfx)) env
  terminal : ∀ (pub : Public) (claims : Claims) (alpha : Alpha) (orig : aspis_core.state_only_prefix.r0.Challenges),
    NMT_CallTree.Event.call "terminal" (pub,claims,alpha,orig) (c.c7 pub claims alpha orig) ∈ (run whole).2 →
    RSL.Spec.map (terminalReply p) (NNG_Interpret136.call events "terminal" (pub,claims,alpha,orig) (c.c7 pub claims alpha orig)) env =
      (VL.terminalQm31.run (p.publicValue pub,p.claims claims,p.alpha alpha,p.original orig)) env
  mask : ∀ (claims : Claims) (alpha : Alpha),
    NMT_CallTree.Event.call "mask" (NNG_FromFnValues136.low claims,NNG_FromFnValues136.high claims,cell claims 27#usize (by decide),alpha) (c.c6 (NNG_FromFnValues136.low claims) (NNG_FromFnValues136.high claims) (cell claims 27#usize (by decide)) alpha) ∈ (run whole).2 →
    RSL.Spec.map (p.q) (NNG_Interpret136.call events "mask" (NNG_FromFnValues136.low claims,NNG_FromFnValues136.high claims,cell claims 27#usize (by decide),alpha) (c.c6 (NNG_FromFnValues136.low claims) (NNG_FromFnValues136.high claims) (cell claims 27#usize (by decide)) alpha)) env =
      (RSL.Spec.pure (VL.maskValue (p.claims claims) (p.alpha alpha))) env
  record25 : ∀ (pfx : r1_wire.Prefix),
    NMT_CallTree.Event.call "record25" (pfx,25#u8) (c.c11 pfx 25#u8) ∈ (run whole).2 →
    RSL.Spec.map (recordReply p) (NNG_Interpret136.call events "record25" (pfx,25#u8) (c.c11 pfx 25#u8)) env =
      (RSL.RE.ofExcept (VL.validatedRecord (p.prefixValue pfx) 25)) env
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
  record26 : ∀ (pfx : r1_wire.Prefix),
    NMT_CallTree.Event.call "record26" (pfx,26#u8) (c.c11 pfx 26#u8) ∈ (run whole).2 →
    RSL.Spec.map (recordReply p) (NNG_Interpret136.call events "record26" (pfx,26#u8) (c.c11 pfx 26#u8)) env =
      (RSL.RE.ofExcept (VL.validatedRecord (p.prefixValue pfx) 26)) env
  beforeZ1 : ∀ (rec : r1_wire.ValidatedRecord),
    NMT_CallTree.Event.call "beforeZ1" (rec,0#usize) (c.c15 29#usize rec 0#usize) ∈ (run whole).2 →
    RSL.Spec.map (decodeReply p) (NNG_Interpret136.call events "beforeZ1" (rec,0#usize) (c.c15 29#usize rec 0#usize)) env =
      (RSL.RE.ofExcept (VL.decodeK29 (p.record rec) 0)) env
  circle1 : ∀ (t : r1_wire.SemanticTranscript H) (rec : r1_wire.ValidatedRecord),
    NMT_CallTree.Event.call "circle1" (t,rec) (c.c13 s.digest t rec) ∈ (run whole).2 →
    RSL.Spec.map (circleReply p) (NNG_Interpret136.call events "circle1" (t,rec) (c.c13 s.digest t rec)) env =
      (VL.circle.run (p.transcript t,p.record rec)) env
  payload2 : ∀ (pfx : r1_wire.Prefix),
    NMT_CallTree.Event.call "payload2" (pfx,2#u8) (c.c12 pfx 2#u8) ∈ (run whole).2 →
    RSL.Spec.map (payloadReply p) (NNG_Interpret136.call events "payload2" (pfx,2#u8) (c.c12 pfx 2#u8)) env =
      (RSL.RE.ofExcept (VL.payload (p.prefixValue pfx) 2)) env

/-- Restriction follows an actual source suffix within the SAME trace, never
an independently chosen invocation. The root starts with within_refl. -/
theorem restrict (VL : RSL.VLib) {H W A B : Type} (p : Representation VL H)
    (c : Calls) (s : Parent H W) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (env : RSL.Env) (whole : Code A) (part : Code B)
    (h : Laws VL p c s events env whole) (within : Within part whole) :
    Laws VL p c s events env part := by
  refine { fromFn := h.fromFn, mapErr := h.mapErr, pointEq := h.pointEq, qeq := h.qeq,
    mark := ?_, rounds := ?_, claims := ?_, terminal := ?_, mask := ?_, record25 := ?_, extra := ?_, multiply := ?_, addMask := ?_, addExtra := ?_, state := ?_, circle0 := ?_, record26 := ?_, beforeZ1 := ?_, circle1 := ?_, payload2 := ?_ }
  · intro site obs i entered
    exact h.mark site obs i (within _ entered)
  · intro pfx t entered
    exact h.rounds pfx t (within _ entered)
  · intro pfx entered
    exact h.claims pfx (within _ entered)
  · intro pub claims alpha orig entered
    exact h.terminal pub claims alpha orig (within _ entered)
  · intro claims alpha entered
    exact h.mask claims alpha (within _ entered)
  · intro pfx entered
    exact h.record25 pfx (within _ entered)
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
  · intro pfx entered
    exact h.record26 pfx (within _ entered)
  · intro rec entered
    exact h.beforeZ1 rec (within _ entered)
  · intro t rec entered
    exact h.circle1 t rec (within _ entered)
  · intro pfx entered
    exact h.payload2 pfx (within _ entered)
#print axioms restrict
end AspisR1.NNG_OccurrenceLaws136
