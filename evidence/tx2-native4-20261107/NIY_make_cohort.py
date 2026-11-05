"""Cohort-side matching source cuts; all associations require kernel compilation."""
from pathlib import Path
import re,json
E=Path(__file__).resolve().parent
mods=['NIY_FirstECut','NIY_AfterKappa','NIY_AfterAlpha0','NIY_AfterAlpha1','NIY_AfterRho','NIY_QueryCut','NIY_ValidationCut','NIY_SemanticCut','NIY_AfterZ0x','NIY_AfterZ0y','NIY_AfterZ1x','NIY_AfterZ1y','NIY_AfterClaim','NIY_AfterRhs','NIY_AfterPower','NIY_AllocationCut','NIY_FinalCut']
mapping={m:'NIY_C_'+m.removeprefix('NIY_') for m in mods};mapping['NIY_FirstRawCut']='NIY_CohortRawCut'
for m in mods:
 s=(E/(m+'.lean')).read_text();s=s.replace('NIY_FirstRawCut.freshAfterRaw','NIY_CohortRawCut.afterRaw')
 for old,new in sorted(mapping.items(),key=lambda p:-len(p[0])):s=s.replace(old,new)
 s=s.replace('NID_ResumeEmission','AspisR1Stage2')
 s=s.replace('(reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)','(ops : ResumeOps)')
 s=s.replace('reserved d bytes v end1 i4','ops bytes v end1 i4')
 for a,b in [('NIL_FreshOps.readE','ops.readE'),('NIL_FreshOps.readK','ops.readK'),('NIL_FreshOps.raw','ops.raw'),('NIL_FreshOps.semantic','ops.readSemanticAlpha'),('NIL_FreshOps.weights','ops.readWeights'),('NIL_FreshOps.validate','ops.validate'),('NIL_TryTransport.fresh','NIL_TryTransport.cohort')]:s=s.replace(a,b)
 s=s.replace('(fun v=>AspisR1.CheckpointBytes4Ops.finalLen (NIL_Carriers.variant v)) v','ops.finalLen v')
 s=s.replace('(ok (NIL_Carriers.unK ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩))','ops.zeroK')
 s=re.sub(r'(?m)^( *)let r51 ←.*?r51 \(\)',lambda z:z[1]+'let r52 ← ops.filled i30 q',s,flags=re.S)
 if m=='NIY_AllocationCut':
  a=s.index(' (do\n   let n ←');b=s.index('   NIL_TryTransport.cohort converted',a)
  s=s[:a]+''' (do
   let n ← ops.finalLen v
   let zero ← ops.zeroK
   let converted ← ops.filled n zero
'''+s[b:]
  s=s.replace(' intro reply\n apply NIL_ResultCases.bind_congr\n intro converted',' intro converted')
 assert 'NIL_FreshOps' not in s,(m,'leftover freshops')
 (E/(mapping[m]+'.lean')).write_text(s)
(E/'NIY_COHORT_MODULES.json').write_text(json.dumps([mapping[m] for m in mods],indent=2)+'\n')
print('Generated 17 cohort-side typed/source cuts matching the actual ResumeOps body; all pending compile.')
