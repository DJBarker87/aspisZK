from pathlib import Path
E=Path(__file__).resolve().parent
# name, typed raw arguments, variable arguments, site, source arguments,
# source Result, value projection, canonical field relation
rows=[
('rounds','(pfx : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H)','pfx t','rounds','(pfx,t)','c.c10 s.digest pfx t','NNG_Projection136.rounds p','VL.semanticRounds.run (p.prefixValue pfx,p.transcript t)'),
('claims','(pfx : r1_wire.Prefix)','pfx','claims','pfx','c.c8 pfx','claimsReply p','VL.claims.run (p.prefixValue pfx)'),
('terminal','(pub : Public) (claims : Claims) (alpha : Alpha) (orig : aspis_core.state_only_prefix.r0.Challenges)','pub claims alpha orig','terminal','(pub,claims,alpha,orig)','c.c7 pub claims alpha orig','terminalReply p','VL.terminalQm31.run (p.publicValue pub,p.claims claims,p.alpha alpha,p.original orig)'),
('mask','(claims : Claims) (alpha : Alpha)','claims alpha','mask','(NNG_FromFnValues136.low claims,NNG_FromFnValues136.high claims,cell claims 27#usize (by decide),alpha)','c.c6 (NNG_FromFnValues136.low claims) (NNG_FromFnValues136.high claims) (cell claims 27#usize (by decide)) alpha','p.q','RSL.Spec.pure (VL.maskValue (p.claims claims) (p.alpha alpha))'),
('record25','(pfx : r1_wire.Prefix)','pfx','record25','(pfx,25#u8)','c.c11 pfx 25#u8','recordReply p','RSL.RE.ofExcept (VL.validatedRecord (p.prefixValue pfx) 25)'),
('extra','(rec : r1_wire.ValidatedRecord)','rec','extra','(rec,87#usize)','c.c15 29#usize rec 87#usize','decodeReply p','RSL.RE.ofExcept (VL.decodeK29 (p.record rec) 87)'),
('multiply','(x y : Q)','x y','multiply','(x,y)','c.c5 x y','p.q','RSL.Spec.pure (VL.qmul (p.q x) (p.q y))'),
('addMask','(x y : Q)','x y','addMask','(x,y)','c.c4 x y','p.q','RSL.Spec.pure (VL.qadd (p.q x) (p.q y))'),
('addExtra','(x y : Q)','x y','addExtra','(x,y)','c.c4 x y','p.q','RSL.Spec.pure (VL.qadd (p.q x) (p.q y))'),
('state','(t : r1_wire.SemanticTranscript H)','t','state','t','c.c14 s.digest t','p.b32','RSL.Spec.pure (VL.state (p.transcript t))'),
('circle0','(t : r1_wire.SemanticTranscript H) (rec : r1_wire.ValidatedRecord)','t rec','circle0','(t,rec)','c.c13 s.digest t rec','circleReply p','VL.circle.run (p.transcript t,p.record rec)'),
('record26','(pfx : r1_wire.Prefix)','pfx','record26','(pfx,26#u8)','c.c11 pfx 26#u8','recordReply p','RSL.RE.ofExcept (VL.validatedRecord (p.prefixValue pfx) 26)'),
('beforeZ1','(rec : r1_wire.ValidatedRecord)','rec','beforeZ1','(rec,0#usize)','c.c15 29#usize rec 0#usize','decodeReply p','RSL.RE.ofExcept (VL.decodeK29 (p.record rec) 0)'),
('circle1','(t : r1_wire.SemanticTranscript H) (rec : r1_wire.ValidatedRecord)','t rec','circle1','(t,rec)','c.c13 s.digest t rec','circleReply p','VL.circle.run (p.transcript t,p.record rec)'),
('payload2','(pfx : r1_wire.Prefix)','pfx','payload2','(pfx,2#u8)','c.c12 pfx 2#u8','payloadReply p','RSL.RE.ofExcept (VL.payload (p.prefixValue pfx) 2)')]
header='''import NNG_EnvObserved136
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
  fromFn : (@Calls.c0 c) = @NNG_StdArray.implementation
  mapErr : (@Calls.c1 c) = @NNG_StdMapErr.run
  pointEq : c.c2 = NNG_Equality136.pointEq
  qeq : c.c3 = NNG_Equality136.qeq
  mark : ∀ (site : String) (obs : NNG_Emitted.Observer) (i : U8),
    NMT_CallTree.Event.call site (obs,i) (c.c9 obs i) ∈ (run whole).2 →
    RSL.Spec.map id (NNG_Interpret136.call events site (obs,i) (c.c9 obs i)) env =
      (RSL.Spec.pure ()) env
'''
s=header
for name,decl,vs,site,arg,r,decode,target in rows:
 s+=f'''  {name} : ∀ {decl},
    NMT_CallTree.Event.call "{site}" {arg} ({r}) ∈ (run whole).2 →
    RSL.Spec.map ({decode}) (NNG_Interpret136.call events "{site}" {arg} ({r})) env =
      ({target}) env
'''
s+='''
/-- Restriction follows an actual source suffix within the SAME trace, never
an independently chosen invocation. The root starts with within_refl. -/
theorem restrict (VL : RSL.VLib) {H W A B : Type} (p : Representation VL H)
    (c : Calls) (s : Parent H W) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (env : RSL.Env) (whole : Code A) (part : Code B)
    (h : Laws VL p c s events env whole) (within : Within part whole) :
    Laws VL p c s events env part := by
  refine ⟨h.fromFn,h.mapErr,h.pointEq,h.qeq,?_'''
for row in rows:s+=',?_'
s+='''⟩
  · intro site obs i entered
    exact h.mark site obs i (within _ entered)
'''
for name,decl,vs,site,arg,r,decode,target in rows:
 s+=f'  · intro {vs} entered\n    exact h.{name} {vs} (within _ entered)\n'
s+='''#print axioms restrict
end AspisR1.NNG_OccurrenceLaws136
'''
(E/'NNG_OccurrenceLaws136.lean').write_text(s)
