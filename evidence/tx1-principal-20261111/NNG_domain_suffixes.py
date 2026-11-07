from pathlib import Path
E=Path(__file__).resolve().parent
# Adapt the already checked source suffix proofs to original semantic input
# retention and the canonical-domain carrier interface. These outputs are
# independently compiled before consumption; old objects earn no new credit.
for name in ['SourceRoot136','SourcePayload136','SourceCircleGuard136']:
 s=(E/('NNG_'+name+'.lean')).read_text()
 for old,new in [('NNG_SourceRoot136','NNG_DSourceRoot136'),('NNG_SourcePayload136','NNG_DSourcePayload136'),('NNG_SourceCircleGuard136','NNG_DSourceCircleGuard136'),('NNG_ProjectionLaws136','NNG_DProjectionLaws136'),('NNG_Projection136','NNG_DProjection136'),('NNG_OccurrenceLaws136','NNG_DOccurrenceLaws136'),('NNG_LawStep136','NNG_DLawStep136')]:s=s.replace(old,new)
 s=s.replace('(VL : RSL.VLib) {H W : Type}', '(VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}')
 s=s.replace('Laws VL p c s','Laws VL a p c s').replace('same_trace VL p c s','same_trace VL a p c s')
 s=s.replace('(args p s)','a')
 if name=='SourceRoot136':
  # value is a constructor model, not an asserted output.
  s=s.replace('(p : Representation VL H) (s : Parent H W)\n', '(p : Representation VL H) (s : Parent H W) (a : RSL.TX1_136.Args VL)\n',1)
  s=s.replace('(VL.c1Root (p.prefixValue s.prefixValue),p.b32 root),p.challenges s.challenges,','(VL.c1Root a.prefix_,p.b32 root),a.challenges,')
  s=s.replace('(p : Representation VL H) (c : Calls) (s : Parent H W)\n', '(p : Representation VL H) (c : Calls) (s : Parent H W)\n    (a : RSL.TX1_136.Args VL) (input : Inputs VL p a s)\n')
  s=s.replace('value p s alpha','value p s a alpha')
  s=s.replace('rw [verified_constructor]','rw [verified_constructor p s a input]')
  s=s.replace('a3 p c s events','a3 p c s a input events')
 else:
  s=s.replace('h.payload2 s.prefixValue ent','h.payload2 ent')
  s=s.replace('VL.payload (p.prefixValue s.prefixValue) 2','VL.payload a.prefix_ 2')
  s=s.replace('NNG_DSourceRoot136.root32 p c s events','NNG_DSourceRoot136.root32 p c s a h.inputs events')
  s=s.replace('NNG_DSourcePayload136.source VL p c s','NNG_DSourcePayload136.source VL a p c s')
  s=s.replace('exact guard VL p c s','exact guard VL a p c s')
 assert 'p.prefixValue' not in s,name
 (E/('NNG_D'+name+'.lean')).write_text(s)
