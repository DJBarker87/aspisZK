import NNG_EmittedPureCall
set_option autoImplicit false
namespace AspisR1.NNG_EmittedOccurrences136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted
open NNG_Observed136 NNG_EmittedCallGraph

/-- Actual emitted rounds occurrence, all outer and inner Result arms.
For rounds, model is CLOSED134's deterministic source model, never its native-cut image. -/
theorem rounds (VL : RSL.VLib) (c : NNG_Emitted.Calls) {H : Type} (d : aspis_core.digest.Digest32 H) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H)
    (sp : VL.Prefix) (st : VL.Transcript) (decode : (core.result.Result (Q × Alpha × r1_wire.SemanticTranscript H) r1_wire.Error) → Except VL.WErr (VL.QM31 × VL.Alpha × VL.Transcript))
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (model : RSL.Env → RSL.Obs (Except VL.WErr (VL.QM31 × VL.Alpha × VL.Transcript)))
    (hd : VL.semanticRounds.dom (sp,st))
    (source : ∀ env, (⟨exit decode (c.c10 d p t),
      events env (.call "rounds" (p,t) (c.c10 d p t))⟩ : RSL.Obs (Except VL.WErr (VL.QM31 × VL.Alpha × VL.Transcript))) = model env)
    (fieldGraph : ∀ env o, VL.semanticRounds.law (sp,st) env o ↔ o = model env) :
    RSL.Spec.map decode (NNG_Interpret136.call events "rounds" (p,t) (c.c10 d p t)) =
      VL.semanticRounds.run (sp,st) :=
  NNG_EmittedCallGraph.closed_at VL.semanticRounds (sp,st) hd decode events "rounds" (p,t)
    (c.c10 d p t) model source fieldGraph
#print axioms rounds

/-- Actual emitted claims occurrence, all outer and inner Result arms.
For rounds, model is CLOSED134's deterministic source model, never its native-cut image. -/
theorem claims (VL : RSL.VLib) (c : NNG_Emitted.Calls) (p : r1_wire.Prefix)
    (sp : VL.Prefix) (decode : (core.result.Result Claims r1_wire.Error) → Except VL.WErr VL.Claims)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (model : RSL.Env → RSL.Obs (Except VL.WErr VL.Claims))
    (hd : VL.claims.dom sp)
    (source : ∀ env, (⟨exit decode (c.c8 p),
      events env (.call "claims" p (c.c8 p))⟩ : RSL.Obs (Except VL.WErr VL.Claims)) = model env)
    (fieldGraph : ∀ env o, VL.claims.law sp env o ↔ o = model env) :
    RSL.Spec.map decode (NNG_Interpret136.call events "claims" p (c.c8 p)) =
      VL.claims.run sp :=
  NNG_EmittedCallGraph.closed_at VL.claims sp hd decode events "claims" p
    (c.c8 p) model source fieldGraph
#print axioms claims

/-- Actual emitted terminal occurrence, all outer and inner Result arms.
For rounds, model is CLOSED134's deterministic source model, never its native-cut image. -/
theorem terminal (VL : RSL.VLib) (c : NNG_Emitted.Calls) (pub : Public) (claims : Claims) (alpha : Alpha) (orig : aspis_core.state_only_prefix.r0.Challenges)
    (spub : VL.Public) (sclaims : VL.Claims) (salpha : VL.Alpha) (sorig : VL.OrigChallenges) (decode : (core.result.Result Q aspis_core.state_only_prefix.r0.Error) → Except Unit VL.QM31)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (model : RSL.Env → RSL.Obs (Except Unit VL.QM31))
    (hd : VL.terminalQm31.dom (spub,sclaims,salpha,sorig))
    (source : ∀ env, (⟨exit decode (c.c7 pub claims alpha orig),
      events env (.call "terminal" (pub,claims,alpha,orig) (c.c7 pub claims alpha orig))⟩ : RSL.Obs (Except Unit VL.QM31)) = model env)
    (fieldGraph : ∀ env o, VL.terminalQm31.law (spub,sclaims,salpha,sorig) env o ↔ o = model env) :
    RSL.Spec.map decode (NNG_Interpret136.call events "terminal" (pub,claims,alpha,orig) (c.c7 pub claims alpha orig)) =
      VL.terminalQm31.run (spub,sclaims,salpha,sorig) :=
  NNG_EmittedCallGraph.closed_at VL.terminalQm31 (spub,sclaims,salpha,sorig) hd decode events "terminal" (pub,claims,alpha,orig)
    (c.c7 pub claims alpha orig) model source fieldGraph
#print axioms terminal

/-- Actual emitted circle0 occurrence, all outer and inner Result arms.
For rounds, model is CLOSED134's deterministic source model, never its native-cut image. -/
theorem circle0 (VL : RSL.VLib) (c : NNG_Emitted.Calls) {H : Type} (d : aspis_core.digest.Digest32 H) (t : r1_wire.SemanticTranscript H) (rec : r1_wire.ValidatedRecord)
    (st : VL.Transcript) (sr : VL.Record) (decode : (core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error × r1_wire.SemanticTranscript H) → Except VL.WErr (VL.Point × VL.Transcript))
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (model : RSL.Env → RSL.Obs (Except VL.WErr (VL.Point × VL.Transcript)))
    (hd : VL.circle.dom (st,sr))
    (source : ∀ env, (⟨exit decode (c.c13 d t rec),
      events env (.call "circle0" (t,rec) (c.c13 d t rec))⟩ : RSL.Obs (Except VL.WErr (VL.Point × VL.Transcript))) = model env)
    (fieldGraph : ∀ env o, VL.circle.law (st,sr) env o ↔ o = model env) :
    RSL.Spec.map decode (NNG_Interpret136.call events "circle0" (t,rec) (c.c13 d t rec)) =
      VL.circle.run (st,sr) :=
  NNG_EmittedCallGraph.closed_at VL.circle (st,sr) hd decode events "circle0" (t,rec)
    (c.c13 d t rec) model source fieldGraph
#print axioms circle0

/-- Actual emitted circle1 occurrence, all outer and inner Result arms.
For rounds, model is CLOSED134's deterministic source model, never its native-cut image. -/
theorem circle1 (VL : RSL.VLib) (c : NNG_Emitted.Calls) {H : Type} (d : aspis_core.digest.Digest32 H) (t : r1_wire.SemanticTranscript H) (rec : r1_wire.ValidatedRecord)
    (st : VL.Transcript) (sr : VL.Record) (decode : (core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error × r1_wire.SemanticTranscript H) → Except VL.WErr (VL.Point × VL.Transcript))
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (model : RSL.Env → RSL.Obs (Except VL.WErr (VL.Point × VL.Transcript)))
    (hd : VL.circle.dom (st,sr))
    (source : ∀ env, (⟨exit decode (c.c13 d t rec),
      events env (.call "circle1" (t,rec) (c.c13 d t rec))⟩ : RSL.Obs (Except VL.WErr (VL.Point × VL.Transcript))) = model env)
    (fieldGraph : ∀ env o, VL.circle.law (st,sr) env o ↔ o = model env) :
    RSL.Spec.map decode (NNG_Interpret136.call events "circle1" (t,rec) (c.c13 d t rec)) =
      VL.circle.run (st,sr) :=
  NNG_EmittedCallGraph.closed_at VL.circle (st,sr) hd decode events "circle1" (t,rec)
    (c.c13 d t rec) model source fieldGraph
#print axioms circle1

/-- The complete actual emitted mask call equals the matching field's
pure graph. Its source law and silence must be supplied from the CLOSED model
on the caller-established domain, not assumed by a final candidate. -/
theorem mask (VL : RSL.VLib) (c : NNG_Emitted.Calls) (a : Array Q 16#usize) (a1 : Alpha) (q : Q) (alpha : Alpha)
    (claims : VL.Claims) (salpha : VL.Alpha) (decode : (Q) → VL.QM31) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (model : VL.QM31)
    (source : resultMap decode (c.c6 a a1 q alpha) = .ok model)
    (fieldGraph : VL.maskValue claims salpha = model)
    (silent : ∀ env, events env (.call "mask" (a,a1,q,alpha) (c.c6 a a1 q alpha)) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "mask" (a,a1,q,alpha) (c.c6 a a1 q alpha)) =
      RSL.Spec.pure (VL.maskValue claims salpha) :=
  NNG_EmittedPureCall.closed_at decode events "mask" (a,a1,q,alpha) (c.c6 a a1 q alpha) model
    (VL.maskValue claims salpha) source fieldGraph silent
#print axioms mask

/-- The complete actual emitted record25 call equals the matching field's
pure graph. Its source law and silence must be supplied from the CLOSED model
on the caller-established domain, not assumed by a final candidate. -/
theorem record25 (VL : RSL.VLib) (c : NNG_Emitted.Calls) (p : r1_wire.Prefix)
    (sp : VL.Prefix) (decode : (core.result.Result r1_wire.ValidatedRecord r1_wire.Error) → Except VL.WErr VL.Record) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (model : Except VL.WErr VL.Record)
    (source : resultMap decode (c.c11 p 25#u8) = .ok model)
    (fieldGraph : VL.validatedRecord sp 25 = model)
    (silent : ∀ env, events env (.call "record25" (p,25#u8) (c.c11 p 25#u8)) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "record25" (p,25#u8) (c.c11 p 25#u8)) =
      RSL.Spec.pure (VL.validatedRecord sp 25) :=
  NNG_EmittedPureCall.closed_at decode events "record25" (p,25#u8) (c.c11 p 25#u8) model
    (VL.validatedRecord sp 25) source fieldGraph silent
#print axioms record25

/-- The complete actual emitted extra call equals the matching field's
pure graph. Its source law and silence must be supplied from the CLOSED model
on the caller-established domain, not assumed by a final candidate. -/
theorem extra (VL : RSL.VLib) (c : NNG_Emitted.Calls) (rec : r1_wire.ValidatedRecord)
    (sr : VL.Record) (decode : (core.result.Result K29 r1_wire.Error) → Except VL.WErr VL.K29) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (model : Except VL.WErr VL.K29)
    (source : resultMap decode (c.c15 29#usize rec 87#usize) = .ok model)
    (fieldGraph : VL.decodeK29 sr 87 = model)
    (silent : ∀ env, events env (.call "extra" (rec,87#usize) (c.c15 29#usize rec 87#usize)) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "extra" (rec,87#usize) (c.c15 29#usize rec 87#usize)) =
      RSL.Spec.pure (VL.decodeK29 sr 87) :=
  NNG_EmittedPureCall.closed_at decode events "extra" (rec,87#usize) (c.c15 29#usize rec 87#usize) model
    (VL.decodeK29 sr 87) source fieldGraph silent
#print axioms extra

/-- The complete actual emitted multiply call equals the matching field's
pure graph. Its source law and silence must be supplied from the CLOSED model
on the caller-established domain, not assumed by a final candidate. -/
theorem multiply (VL : RSL.VLib) (c : NNG_Emitted.Calls) (x y : Q)
    (sx sy : VL.QM31) (decode : (Q) → VL.QM31) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (model : VL.QM31)
    (source : resultMap decode (c.c5 x y) = .ok model)
    (fieldGraph : VL.qmul sx sy = model)
    (silent : ∀ env, events env (.call "multiply" (x,y) (c.c5 x y)) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "multiply" (x,y) (c.c5 x y)) =
      RSL.Spec.pure (VL.qmul sx sy) :=
  NNG_EmittedPureCall.closed_at decode events "multiply" (x,y) (c.c5 x y) model
    (VL.qmul sx sy) source fieldGraph silent
#print axioms multiply

/-- The complete actual emitted addMask call equals the matching field's
pure graph. Its source law and silence must be supplied from the CLOSED model
on the caller-established domain, not assumed by a final candidate. -/
theorem addMask (VL : RSL.VLib) (c : NNG_Emitted.Calls) (x y : Q)
    (sx sy : VL.QM31) (decode : (Q) → VL.QM31) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (model : VL.QM31)
    (source : resultMap decode (c.c4 x y) = .ok model)
    (fieldGraph : VL.qadd sx sy = model)
    (silent : ∀ env, events env (.call "addMask" (x,y) (c.c4 x y)) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "addMask" (x,y) (c.c4 x y)) =
      RSL.Spec.pure (VL.qadd sx sy) :=
  NNG_EmittedPureCall.closed_at decode events "addMask" (x,y) (c.c4 x y) model
    (VL.qadd sx sy) source fieldGraph silent
#print axioms addMask

/-- The complete actual emitted addExtra call equals the matching field's
pure graph. Its source law and silence must be supplied from the CLOSED model
on the caller-established domain, not assumed by a final candidate. -/
theorem addExtra (VL : RSL.VLib) (c : NNG_Emitted.Calls) (x y : Q)
    (sx sy : VL.QM31) (decode : (Q) → VL.QM31) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (model : VL.QM31)
    (source : resultMap decode (c.c4 x y) = .ok model)
    (fieldGraph : VL.qadd sx sy = model)
    (silent : ∀ env, events env (.call "addExtra" (x,y) (c.c4 x y)) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "addExtra" (x,y) (c.c4 x y)) =
      RSL.Spec.pure (VL.qadd sx sy) :=
  NNG_EmittedPureCall.closed_at decode events "addExtra" (x,y) (c.c4 x y) model
    (VL.qadd sx sy) source fieldGraph silent
#print axioms addExtra

/-- The complete actual emitted record26 call equals the matching field's
pure graph. Its source law and silence must be supplied from the CLOSED model
on the caller-established domain, not assumed by a final candidate. -/
theorem record26 (VL : RSL.VLib) (c : NNG_Emitted.Calls) (p : r1_wire.Prefix)
    (sp : VL.Prefix) (decode : (core.result.Result r1_wire.ValidatedRecord r1_wire.Error) → Except VL.WErr VL.Record) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (model : Except VL.WErr VL.Record)
    (source : resultMap decode (c.c11 p 26#u8) = .ok model)
    (fieldGraph : VL.validatedRecord sp 26 = model)
    (silent : ∀ env, events env (.call "record26" (p,26#u8) (c.c11 p 26#u8)) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "record26" (p,26#u8) (c.c11 p 26#u8)) =
      RSL.Spec.pure (VL.validatedRecord sp 26) :=
  NNG_EmittedPureCall.closed_at decode events "record26" (p,26#u8) (c.c11 p 26#u8) model
    (VL.validatedRecord sp 26) source fieldGraph silent
#print axioms record26

/-- The complete actual emitted beforeZ1 call equals the matching field's
pure graph. Its source law and silence must be supplied from the CLOSED model
on the caller-established domain, not assumed by a final candidate. -/
theorem beforeZ1 (VL : RSL.VLib) (c : NNG_Emitted.Calls) (rec : r1_wire.ValidatedRecord)
    (sr : VL.Record) (decode : (core.result.Result K29 r1_wire.Error) → Except VL.WErr VL.K29) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (model : Except VL.WErr VL.K29)
    (source : resultMap decode (c.c15 29#usize rec 0#usize) = .ok model)
    (fieldGraph : VL.decodeK29 sr 0 = model)
    (silent : ∀ env, events env (.call "beforeZ1" (rec,0#usize) (c.c15 29#usize rec 0#usize)) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "beforeZ1" (rec,0#usize) (c.c15 29#usize rec 0#usize)) =
      RSL.Spec.pure (VL.decodeK29 sr 0) :=
  NNG_EmittedPureCall.closed_at decode events "beforeZ1" (rec,0#usize) (c.c15 29#usize rec 0#usize) model
    (VL.decodeK29 sr 0) source fieldGraph silent
#print axioms beforeZ1

/-- The complete actual emitted payload2 call equals the matching field's
pure graph. Its source law and silence must be supplied from the CLOSED model
on the caller-established domain, not assumed by a final candidate. -/
theorem payload2 (VL : RSL.VLib) (c : NNG_Emitted.Calls) (p : r1_wire.Prefix)
    (sp : VL.Prefix) (decode : (core.result.Result (Slice U8) r1_wire.Error) → Except VL.WErr RSL.Bytes) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (model : Except VL.WErr RSL.Bytes)
    (source : resultMap decode (c.c12 p 2#u8) = .ok model)
    (fieldGraph : VL.payload sp 2 = model)
    (silent : ∀ env, events env (.call "payload2" (p,2#u8) (c.c12 p 2#u8)) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "payload2" (p,2#u8) (c.c12 p 2#u8)) =
      RSL.Spec.pure (VL.payload sp 2) :=
  NNG_EmittedPureCall.closed_at decode events "payload2" (p,2#u8) (c.c12 p 2#u8) model
    (VL.payload sp 2) source fieldGraph silent
#print axioms payload2
end AspisR1.NNG_EmittedOccurrences136
