import NNG_EnvCallGraph136
set_option autoImplicit false
namespace AspisR1.NNG_EnvOccurrences136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted
open NNG_Observed136 NNG_EmittedCallGraph

/-- SAME emitted rounds call at the actual environment. The field and call
must be graphs of the SAME CLOSED deterministic model at this Env. -/
theorem rounds (VL : RSL.VLib) (c : NNG_Emitted.Calls) {H : Type} (d : aspis_core.digest.Digest32 H) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H)
    (sp : VL.Prefix) (st : VL.Transcript) (decode : (core.result.Result (Q × Alpha × r1_wire.SemanticTranscript H) r1_wire.Error) → Except VL.WErr (VL.QM31 × VL.Alpha × VL.Transcript))
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env) (model : RSL.Obs (Except VL.WErr (VL.QM31 × VL.Alpha × VL.Transcript)))
    (hd : VL.semanticRounds.dom (sp,st))
    (source : (⟨exit decode (c.c10 d p t),
      events env (.call "rounds" (p,t) (c.c10 d p t))⟩ : RSL.Obs (Except VL.WErr (VL.QM31 × VL.Alpha × VL.Transcript))) = model)
    (fieldGraph : ∀ o, VL.semanticRounds.law (sp,st) env o ↔ o = model) :
    RSL.Spec.map decode (NNG_Interpret136.call events "rounds" (p,t) (c.c10 d p t)) env =
      VL.semanticRounds.run (sp,st) env :=
  NNG_EnvCallGraph136.effect_at VL.semanticRounds (sp,st) hd decode events "rounds" (p,t)
    (c.c10 d p t) env model source fieldGraph
#print axioms rounds

/-- SAME emitted claims call at the actual environment. The field and call
must be graphs of the SAME CLOSED deterministic model at this Env. -/
theorem claims (VL : RSL.VLib) (c : NNG_Emitted.Calls) (p : r1_wire.Prefix)
    (sp : VL.Prefix) (decode : (core.result.Result Claims r1_wire.Error) → Except VL.WErr VL.Claims)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env) (model : RSL.Obs (Except VL.WErr VL.Claims))
    (hd : VL.claims.dom sp)
    (source : (⟨exit decode (c.c8 p),
      events env (.call "claims" p (c.c8 p))⟩ : RSL.Obs (Except VL.WErr VL.Claims)) = model)
    (fieldGraph : ∀ o, VL.claims.law sp env o ↔ o = model) :
    RSL.Spec.map decode (NNG_Interpret136.call events "claims" p (c.c8 p)) env =
      VL.claims.run sp env :=
  NNG_EnvCallGraph136.effect_at VL.claims sp hd decode events "claims" p
    (c.c8 p) env model source fieldGraph
#print axioms claims

/-- SAME emitted terminal call at the actual environment. The field and call
must be graphs of the SAME CLOSED deterministic model at this Env. -/
theorem terminal (VL : RSL.VLib) (c : NNG_Emitted.Calls) (pub : Public) (claims : Claims) (alpha : Alpha) (orig : aspis_core.state_only_prefix.r0.Challenges)
    (spub : VL.Public) (sclaims : VL.Claims) (salpha : VL.Alpha) (sorig : VL.OrigChallenges) (decode : (core.result.Result Q aspis_core.state_only_prefix.r0.Error) → Except Unit VL.QM31)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env) (model : RSL.Obs (Except Unit VL.QM31))
    (hd : VL.terminalQm31.dom (spub,sclaims,salpha,sorig))
    (source : (⟨exit decode (c.c7 pub claims alpha orig),
      events env (.call "terminal" (pub,claims,alpha,orig) (c.c7 pub claims alpha orig))⟩ : RSL.Obs (Except Unit VL.QM31)) = model)
    (fieldGraph : ∀ o, VL.terminalQm31.law (spub,sclaims,salpha,sorig) env o ↔ o = model) :
    RSL.Spec.map decode (NNG_Interpret136.call events "terminal" (pub,claims,alpha,orig) (c.c7 pub claims alpha orig)) env =
      VL.terminalQm31.run (spub,sclaims,salpha,sorig) env :=
  NNG_EnvCallGraph136.effect_at VL.terminalQm31 (spub,sclaims,salpha,sorig) hd decode events "terminal" (pub,claims,alpha,orig)
    (c.c7 pub claims alpha orig) env model source fieldGraph
#print axioms terminal

/-- SAME emitted circle0 call at the actual environment. The field and call
must be graphs of the SAME CLOSED deterministic model at this Env. -/
theorem circle0 (VL : RSL.VLib) (c : NNG_Emitted.Calls) {H : Type} (d : aspis_core.digest.Digest32 H) (t : r1_wire.SemanticTranscript H) (rec : r1_wire.ValidatedRecord)
    (st : VL.Transcript) (sr : VL.Record) (decode : (core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error × r1_wire.SemanticTranscript H) → Except VL.WErr (VL.Point × VL.Transcript))
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env) (model : RSL.Obs (Except VL.WErr (VL.Point × VL.Transcript)))
    (hd : VL.circle.dom (st,sr))
    (source : (⟨exit decode (c.c13 d t rec),
      events env (.call "circle0" (t,rec) (c.c13 d t rec))⟩ : RSL.Obs (Except VL.WErr (VL.Point × VL.Transcript))) = model)
    (fieldGraph : ∀ o, VL.circle.law (st,sr) env o ↔ o = model) :
    RSL.Spec.map decode (NNG_Interpret136.call events "circle0" (t,rec) (c.c13 d t rec)) env =
      VL.circle.run (st,sr) env :=
  NNG_EnvCallGraph136.effect_at VL.circle (st,sr) hd decode events "circle0" (t,rec)
    (c.c13 d t rec) env model source fieldGraph
#print axioms circle0

/-- SAME emitted circle1 call at the actual environment. The field and call
must be graphs of the SAME CLOSED deterministic model at this Env. -/
theorem circle1 (VL : RSL.VLib) (c : NNG_Emitted.Calls) {H : Type} (d : aspis_core.digest.Digest32 H) (t : r1_wire.SemanticTranscript H) (rec : r1_wire.ValidatedRecord)
    (st : VL.Transcript) (sr : VL.Record) (decode : (core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error × r1_wire.SemanticTranscript H) → Except VL.WErr (VL.Point × VL.Transcript))
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env) (model : RSL.Obs (Except VL.WErr (VL.Point × VL.Transcript)))
    (hd : VL.circle.dom (st,sr))
    (source : (⟨exit decode (c.c13 d t rec),
      events env (.call "circle1" (t,rec) (c.c13 d t rec))⟩ : RSL.Obs (Except VL.WErr (VL.Point × VL.Transcript))) = model)
    (fieldGraph : ∀ o, VL.circle.law (st,sr) env o ↔ o = model) :
    RSL.Spec.map decode (NNG_Interpret136.call events "circle1" (t,rec) (c.c13 d t rec)) env =
      VL.circle.run (st,sr) env :=
  NNG_EnvCallGraph136.effect_at VL.circle (st,sr) hd decode events "circle1" (t,rec)
    (c.c13 d t rec) env model source fieldGraph
#print axioms circle1

/-- Actual emitted mask: exact returned value (inner Err included), with
silence proved at the same environment. This is an occurrence law, not a
VLib field instance or a final root premise. -/
theorem mask (VL : RSL.VLib) (c : NNG_Emitted.Calls) (a : Array Q 16#usize) (a1 : Alpha) (q : Q) (alpha : Alpha)
    (claims : VL.Claims) (salpha : VL.Alpha) (decode : (Q) → VL.QM31) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env) (model : VL.QM31)
    (source : resultMap decode (c.c6 a a1 q alpha) = .ok model)
    (fieldGraph : VL.maskValue claims salpha = model)
    (silent : events env (.call "mask" (a,a1,q,alpha) (c.c6 a a1 q alpha)) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "mask" (a,a1,q,alpha) (c.c6 a a1 q alpha)) env =
      (RSL.Spec.pure (VL.maskValue claims salpha)) env :=
  NNG_EnvCallGraph136.pure_at decode events "mask" (a,a1,q,alpha) (c.c6 a a1 q alpha) env model
    (VL.maskValue claims salpha) source fieldGraph silent
#print axioms mask

/-- Actual emitted record25: exact returned value (inner Err included), with
silence proved at the same environment. This is an occurrence law, not a
VLib field instance or a final root premise. -/
theorem record25 (VL : RSL.VLib) (c : NNG_Emitted.Calls) (p : r1_wire.Prefix)
    (sp : VL.Prefix) (decode : (core.result.Result r1_wire.ValidatedRecord r1_wire.Error) → Except VL.WErr VL.Record) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env) (model : Except VL.WErr VL.Record)
    (source : resultMap decode (c.c11 p 25#u8) = .ok model)
    (fieldGraph : VL.validatedRecord sp 25 = model)
    (silent : events env (.call "record25" (p,25#u8) (c.c11 p 25#u8)) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "record25" (p,25#u8) (c.c11 p 25#u8)) env =
      (RSL.Spec.pure (VL.validatedRecord sp 25)) env :=
  NNG_EnvCallGraph136.pure_at decode events "record25" (p,25#u8) (c.c11 p 25#u8) env model
    (VL.validatedRecord sp 25) source fieldGraph silent
#print axioms record25

/-- Actual emitted extra: exact returned value (inner Err included), with
silence proved at the same environment. This is an occurrence law, not a
VLib field instance or a final root premise. -/
theorem extra (VL : RSL.VLib) (c : NNG_Emitted.Calls) (rec : r1_wire.ValidatedRecord)
    (sr : VL.Record) (decode : (core.result.Result K29 r1_wire.Error) → Except VL.WErr VL.K29) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env) (model : Except VL.WErr VL.K29)
    (source : resultMap decode (c.c15 29#usize rec 87#usize) = .ok model)
    (fieldGraph : VL.decodeK29 sr 87 = model)
    (silent : events env (.call "extra" (rec,87#usize) (c.c15 29#usize rec 87#usize)) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "extra" (rec,87#usize) (c.c15 29#usize rec 87#usize)) env =
      (RSL.Spec.pure (VL.decodeK29 sr 87)) env :=
  NNG_EnvCallGraph136.pure_at decode events "extra" (rec,87#usize) (c.c15 29#usize rec 87#usize) env model
    (VL.decodeK29 sr 87) source fieldGraph silent
#print axioms extra

/-- Actual emitted multiply: exact returned value (inner Err included), with
silence proved at the same environment. This is an occurrence law, not a
VLib field instance or a final root premise. -/
theorem multiply (VL : RSL.VLib) (c : NNG_Emitted.Calls) (x y : Q)
    (sx sy : VL.QM31) (decode : (Q) → VL.QM31) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env) (model : VL.QM31)
    (source : resultMap decode (c.c5 x y) = .ok model)
    (fieldGraph : VL.qmul sx sy = model)
    (silent : events env (.call "multiply" (x,y) (c.c5 x y)) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "multiply" (x,y) (c.c5 x y)) env =
      (RSL.Spec.pure (VL.qmul sx sy)) env :=
  NNG_EnvCallGraph136.pure_at decode events "multiply" (x,y) (c.c5 x y) env model
    (VL.qmul sx sy) source fieldGraph silent
#print axioms multiply

/-- Actual emitted addMask: exact returned value (inner Err included), with
silence proved at the same environment. This is an occurrence law, not a
VLib field instance or a final root premise. -/
theorem addMask (VL : RSL.VLib) (c : NNG_Emitted.Calls) (x y : Q)
    (sx sy : VL.QM31) (decode : (Q) → VL.QM31) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env) (model : VL.QM31)
    (source : resultMap decode (c.c4 x y) = .ok model)
    (fieldGraph : VL.qadd sx sy = model)
    (silent : events env (.call "addMask" (x,y) (c.c4 x y)) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "addMask" (x,y) (c.c4 x y)) env =
      (RSL.Spec.pure (VL.qadd sx sy)) env :=
  NNG_EnvCallGraph136.pure_at decode events "addMask" (x,y) (c.c4 x y) env model
    (VL.qadd sx sy) source fieldGraph silent
#print axioms addMask

/-- Actual emitted addExtra: exact returned value (inner Err included), with
silence proved at the same environment. This is an occurrence law, not a
VLib field instance or a final root premise. -/
theorem addExtra (VL : RSL.VLib) (c : NNG_Emitted.Calls) (x y : Q)
    (sx sy : VL.QM31) (decode : (Q) → VL.QM31) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env) (model : VL.QM31)
    (source : resultMap decode (c.c4 x y) = .ok model)
    (fieldGraph : VL.qadd sx sy = model)
    (silent : events env (.call "addExtra" (x,y) (c.c4 x y)) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "addExtra" (x,y) (c.c4 x y)) env =
      (RSL.Spec.pure (VL.qadd sx sy)) env :=
  NNG_EnvCallGraph136.pure_at decode events "addExtra" (x,y) (c.c4 x y) env model
    (VL.qadd sx sy) source fieldGraph silent
#print axioms addExtra

/-- Actual emitted record26: exact returned value (inner Err included), with
silence proved at the same environment. This is an occurrence law, not a
VLib field instance or a final root premise. -/
theorem record26 (VL : RSL.VLib) (c : NNG_Emitted.Calls) (p : r1_wire.Prefix)
    (sp : VL.Prefix) (decode : (core.result.Result r1_wire.ValidatedRecord r1_wire.Error) → Except VL.WErr VL.Record) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env) (model : Except VL.WErr VL.Record)
    (source : resultMap decode (c.c11 p 26#u8) = .ok model)
    (fieldGraph : VL.validatedRecord sp 26 = model)
    (silent : events env (.call "record26" (p,26#u8) (c.c11 p 26#u8)) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "record26" (p,26#u8) (c.c11 p 26#u8)) env =
      (RSL.Spec.pure (VL.validatedRecord sp 26)) env :=
  NNG_EnvCallGraph136.pure_at decode events "record26" (p,26#u8) (c.c11 p 26#u8) env model
    (VL.validatedRecord sp 26) source fieldGraph silent
#print axioms record26

/-- Actual emitted beforeZ1: exact returned value (inner Err included), with
silence proved at the same environment. This is an occurrence law, not a
VLib field instance or a final root premise. -/
theorem beforeZ1 (VL : RSL.VLib) (c : NNG_Emitted.Calls) (rec : r1_wire.ValidatedRecord)
    (sr : VL.Record) (decode : (core.result.Result K29 r1_wire.Error) → Except VL.WErr VL.K29) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env) (model : Except VL.WErr VL.K29)
    (source : resultMap decode (c.c15 29#usize rec 0#usize) = .ok model)
    (fieldGraph : VL.decodeK29 sr 0 = model)
    (silent : events env (.call "beforeZ1" (rec,0#usize) (c.c15 29#usize rec 0#usize)) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "beforeZ1" (rec,0#usize) (c.c15 29#usize rec 0#usize)) env =
      (RSL.Spec.pure (VL.decodeK29 sr 0)) env :=
  NNG_EnvCallGraph136.pure_at decode events "beforeZ1" (rec,0#usize) (c.c15 29#usize rec 0#usize) env model
    (VL.decodeK29 sr 0) source fieldGraph silent
#print axioms beforeZ1

/-- Actual emitted payload2: exact returned value (inner Err included), with
silence proved at the same environment. This is an occurrence law, not a
VLib field instance or a final root premise. -/
theorem payload2 (VL : RSL.VLib) (c : NNG_Emitted.Calls) (p : r1_wire.Prefix)
    (sp : VL.Prefix) (decode : (core.result.Result (Slice U8) r1_wire.Error) → Except VL.WErr RSL.Bytes) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env) (model : Except VL.WErr RSL.Bytes)
    (source : resultMap decode (c.c12 p 2#u8) = .ok model)
    (fieldGraph : VL.payload sp 2 = model)
    (silent : events env (.call "payload2" (p,2#u8) (c.c12 p 2#u8)) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "payload2" (p,2#u8) (c.c12 p 2#u8)) env =
      (RSL.Spec.pure (VL.payload sp 2)) env :=
  NNG_EnvCallGraph136.pure_at decode events "payload2" (p,2#u8) (c.c12 p 2#u8) env model
    (VL.payload sp 2) source fieldGraph silent
#print axioms payload2
end AspisR1.NNG_EnvOccurrences136
