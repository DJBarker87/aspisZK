from pathlib import Path
E=Path(__file__).resolve().parent
rows=[
('rounds','','','rounds','(s.prefixValue,s.transcript)','c.c10 s.digest s.prefixValue s.transcript','NNG_DProjection136.rounds p','VL.semanticRounds.run (a.prefix_,a.transcript)'),
('claims','','','claims','s.prefixValue','c.c8 s.prefixValue','claimsReply p','VL.claims.run a.prefix_'),
('terminal','(claims : Claims) (alpha : Alpha)','claims alpha','terminal','(s.publicValue,claims,alpha,s.challenges)','c.c7 s.publicValue claims alpha s.challenges','terminalReply p','VL.terminalQm31.run (a.public_,p.claims claims,p.alpha alpha,VL.origChallenges a.challenges)'),
('mask','(claims : Claims) (alpha : Alpha)','claims alpha','mask','(NNG_FromFnValues136.low claims,NNG_FromFnValues136.high claims,cell claims 27#usize (by decide),alpha)','c.c6 (NNG_FromFnValues136.low claims) (NNG_FromFnValues136.high claims) (cell claims 27#usize (by decide)) alpha','p.q','RSL.Spec.pure (VL.maskValue (p.claims claims) (p.alpha alpha))'),
('record25','','','record25','(s.prefixValue,25#u8)','c.c11 s.prefixValue 25#u8','recordReply p','RSL.RE.ofExcept (VL.validatedRecord a.prefix_ 25)'),
('extra','(rec : r1_wire.ValidatedRecord)','rec','extra','(rec,87#usize)','c.c15 29#usize rec 87#usize','decodeReply p','RSL.RE.ofExcept (VL.decodeK29 (p.record rec) 87)'),
('multiply','(x y : Q)','x y','multiply','(x,y)','c.c5 x y','p.q','RSL.Spec.pure (VL.qmul (p.q x) (p.q y))'),
('addMask','(x y : Q)','x y','addMask','(x,y)','c.c4 x y','p.q','RSL.Spec.pure (VL.qadd (p.q x) (p.q y))'),
('addExtra','(x y : Q)','x y','addExtra','(x,y)','c.c4 x y','p.q','RSL.Spec.pure (VL.qadd (p.q x) (p.q y))'),
('state','(t : r1_wire.SemanticTranscript H)','t','state','t','c.c14 s.digest t','p.b32','RSL.Spec.pure (VL.state (p.transcript t))'),
('circle0','(t : r1_wire.SemanticTranscript H) (rec : r1_wire.ValidatedRecord)','t rec','circle0','(t,rec)','c.c13 s.digest t rec','circleReply p','VL.circle.run (p.transcript t,p.record rec)'),
('record26','','','record26','(s.prefixValue,26#u8)','c.c11 s.prefixValue 26#u8','recordReply p','RSL.RE.ofExcept (VL.validatedRecord a.prefix_ 26)'),
('beforeZ1','(rec : r1_wire.ValidatedRecord)','rec','beforeZ1','(rec,0#usize)','c.c15 29#usize rec 0#usize','decodeReply p','RSL.RE.ofExcept (VL.decodeK29 (p.record rec) 0)'),
('circle1','(t : r1_wire.SemanticTranscript H) (rec : r1_wire.ValidatedRecord)','t rec','circle1','(t,rec)','c.c13 s.digest t rec','circleReply p','VL.circle.run (p.transcript t,p.record rec)'),
('payload2','','','payload2','(s.prefixValue,2#u8)','c.c12 s.prefixValue 2#u8','payloadReply p','RSL.RE.ofExcept (VL.payload a.prefix_ 2)')]
s='''import NNG_DEnvObserved136
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
'''
for name,decl,vs,site,arg,r,decode,target in rows:
 quant=f'∀ {decl},' if decl else ''
 s+=f'''  {name} : {quant}
    NMT_CallTree.Event.call "{site}" {arg} ({r}) ∈ (run whole).2 →
    RSL.Spec.map ({decode}) (NNG_Interpret136.call events "{site}" {arg} ({r})) env =
      ({target}) env
'''
s+='''  roundsCanonical :
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
  refine ⟨h.inputs,h.fromFn,h.mapErr,h.pointEq,h.qeq,?_'''
for r in rows:s+=',?_'
s+=',?_,?_⟩\n'
s+='''  · intro site obs i entered
    exact h.mark site obs i (within _ entered)
'''
for name,decl,vs,site,arg,r,decode,target in rows:
 s+=f'  · intro {vs+" " if vs else ""}entered\n    exact h.{name} {vs+" " if vs else ""}(within _ entered)\n'
s+='''  · intro entered running alpha t1 returned
    exact h.roundsCanonical (within _ entered) running alpha t1 returned
  · intro x y entered z returned
    exact h.addExtraCanonical x y (within _ entered) z returned
#print axioms restrict
end AspisR1.NNG_DOccurrenceLaws136
'''
(E/'NNG_DOccurrenceLaws136.lean').write_text(s)
