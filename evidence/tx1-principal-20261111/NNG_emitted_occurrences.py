from pathlib import Path
E=Path(__file__).resolve().parent
s='''import NNG_EmittedPureCall
set_option autoImplicit false
namespace AspisR1.NNG_EmittedOccurrences136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted
open NNG_Observed136 NNG_EmittedCallGraph
'''
Event='RSL.Env → NMT_CallTree.Event → List RSL.Event'
fx=[
 ('rounds','semanticRounds','{H : Type} (d : aspis_core.digest.Digest32 H) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H)',
  '(sp : VL.Prefix) (st : VL.Transcript)','(sp,st)','(p,t)','c.c10 d p t',
  'core.result.Result (Q × Alpha × r1_wire.SemanticTranscript H) r1_wire.Error','Except VL.WErr (VL.QM31 × VL.Alpha × VL.Transcript)'),
 ('claims','claims','(p : r1_wire.Prefix)','(sp : VL.Prefix)','sp','p','c.c8 p',
  'core.result.Result Claims r1_wire.Error','Except VL.WErr VL.Claims'),
 ('terminal','terminalQm31','(pub : Public) (claims : Claims) (alpha : Alpha) (orig : aspis_core.state_only_prefix.r0.Challenges)',
  '(spub : VL.Public) (sclaims : VL.Claims) (salpha : VL.Alpha) (sorig : VL.OrigChallenges)',
  '(spub,sclaims,salpha,sorig)','(pub,claims,alpha,orig)','c.c7 pub claims alpha orig',
  'core.result.Result Q aspis_core.state_only_prefix.r0.Error','Except Unit VL.QM31')]
for site in ['circle0','circle1']:
 fx.append((site,'circle','{H : Type} (d : aspis_core.digest.Digest32 H) (t : r1_wire.SemanticTranscript H) (rec : r1_wire.ValidatedRecord)',
 '(st : VL.Transcript) (sr : VL.Record)','(st,sr)','(t,rec)','c.c13 d t rec',
 'core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error × r1_wire.SemanticTranscript H',
 'Except VL.WErr (VL.Point × VL.Transcript)'))
for site,field,rawargs,semargs,arg,rawarg,raw,ret,semret in fx:
 s+=f'''\n/-- Actual emitted {site} occurrence, all outer and inner Result arms.
For rounds, model is CLOSED134's deterministic source model, never its native-cut image. -/
theorem {site} (VL : RSL.VLib) (c : NNG_Emitted.Calls) {rawargs}
    {semargs} (decode : ({ret}) → {semret})
    (events : {Event}) (model : RSL.Env → RSL.Obs ({semret}))
    (hd : VL.{field}.dom {arg})
    (source : ∀ env, (⟨exit decode ({raw}),
      events env (.call "{site}" {rawarg} ({raw}))⟩ : RSL.Obs ({semret})) = model env)
    (fieldGraph : ∀ env o, VL.{field}.law {arg} env o ↔ o = model env) :
    RSL.Spec.map decode (NNG_Interpret136.call events "{site}" {rawarg} ({raw})) =
      VL.{field}.run {arg} :=
  NNG_EmittedCallGraph.closed_at VL.{field} {arg} hd decode events "{site}" {rawarg}
    ({raw}) model source fieldGraph
#print axioms {site}
'''
pure=[
 ('mask','maskValue','(a : Array Q 16#usize) (a1 : Alpha) (q : Q) (alpha : Alpha)',
  '(claims : VL.Claims) (salpha : VL.Alpha)','claims salpha','(a,a1,q,alpha)','c.c6 a a1 q alpha','Q','VL.QM31'),
 ('record25','validatedRecord','(p : r1_wire.Prefix)','(sp : VL.Prefix)','sp 25','(p,25#u8)','c.c11 p 25#u8','core.result.Result r1_wire.ValidatedRecord r1_wire.Error','Except VL.WErr VL.Record'),
 ('extra','decodeK29','(rec : r1_wire.ValidatedRecord)','(sr : VL.Record)','sr 87','(rec,87#usize)','c.c15 29#usize rec 87#usize','core.result.Result K29 r1_wire.Error','Except VL.WErr VL.K29'),
 ('multiply','qmul','(x y : Q)','(sx sy : VL.QM31)','sx sy','(x,y)','c.c5 x y','Q','VL.QM31'),
 ('addMask','qadd','(x y : Q)','(sx sy : VL.QM31)','sx sy','(x,y)','c.c4 x y','Q','VL.QM31'),
 ('addExtra','qadd','(x y : Q)','(sx sy : VL.QM31)','sx sy','(x,y)','c.c4 x y','Q','VL.QM31'),
 ('record26','validatedRecord','(p : r1_wire.Prefix)','(sp : VL.Prefix)','sp 26','(p,26#u8)','c.c11 p 26#u8','core.result.Result r1_wire.ValidatedRecord r1_wire.Error','Except VL.WErr VL.Record'),
 ('beforeZ1','decodeK29','(rec : r1_wire.ValidatedRecord)','(sr : VL.Record)','sr 0','(rec,0#usize)','c.c15 29#usize rec 0#usize','core.result.Result K29 r1_wire.Error','Except VL.WErr VL.K29'),
 ('payload2','payload','(p : r1_wire.Prefix)','(sp : VL.Prefix)','sp 2','(p,2#u8)','c.c12 p 2#u8','core.result.Result (Slice U8) r1_wire.Error','Except VL.WErr RSL.Bytes')]
for site,field,rawargs,semargs,arg,rawarg,raw,ret,semret in pure:
 s+=f'''\n/-- The complete actual emitted {site} call equals the matching field's
pure graph. Its source law and silence must be supplied from the CLOSED model
on the caller-established domain, not assumed by a final candidate. -/
theorem {site} (VL : RSL.VLib) (c : NNG_Emitted.Calls) {rawargs}
    {semargs} (decode : ({ret}) → {semret}) (events : {Event}) (model : {semret})
    (source : resultMap decode ({raw}) = .ok model)
    (fieldGraph : VL.{field} {arg} = model)
    (silent : ∀ env, events env (.call "{site}" {rawarg} ({raw})) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "{site}" {rawarg} ({raw})) =
      RSL.Spec.pure (VL.{field} {arg}) :=
  NNG_EmittedPureCall.closed_at decode events "{site}" {rawarg} ({raw}) model
    (VL.{field} {arg}) source fieldGraph silent
#print axioms {site}
'''
s+='end AspisR1.NNG_EmittedOccurrences136\n'
(E/'NNG_EmittedOccurrences136.lean').write_text(s)
