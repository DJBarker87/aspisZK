"""Literal query/absorb emissions, logging digest calls rather than phase tags."""
from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l1-20261028';D=R/'docs/research/v8-r0-zk-20261009/lean'
s=json.loads((E/'focused-project-sources.json').read_text())['R1Z.ProverRwFullFuns']
def source(n):
 a=s.index('def '+n+'\n');b=s.index('\n/--',a);raw=s[a:b];h,body=raw.split('\n  := do\n',1);sig=h[len('def '+n):];pos=sig.rfind('\n  Result');return raw,sig[:pos],sig[pos:].replace('\n  Result','\n  Logged',1),body

def instrument(body,first,absorb=False):
 lines=body.splitlines()
 for at in reversed(range(len(lines))):
  line=lines[at]
  if '←' not in line or not re.match(r'\s*let\b',line):continue
  indent=len(line)-len(line.lstrip());end=at+1
  while end<len(lines) and (not lines[end].strip() or len(lines[end])-len(lines[end].lstrip())>indent):end+=1
  prefix,text=line.split('←',1);expr='\n'.join([text.strip()]+lines[at+1:end]).strip()
  if not absorb and expr.startswith('host_transcript.Transcript.absorb '):
   expr=expr.replace('host_transcript.Transcript.absorb','PV_L1_QueryAbsorb.produce',1);lines[at:end]=[prefix+'← '+expr]
  else:lines[at:end]=[prefix+'← PV_L1_Logged.lift ('+expr+')']
 body='\n'.join(lines);counter=[first]
 def mark(m):
  i=counter[0];counter[0]+=1;return 'observe .queryScan '+str(i)+' ('+m[1]+')'
 body=re.sub(r'PV_L1_Logged.lift \((aspis_coredigestDigest32Inst\.digest [^\n]*)\)',mark,body)
 return re.sub(r'(?<![A-Za-z0-9_.])ok(?=\s|\()', 'Pure.pure',body),counter[0]-first

base='''import PV_L1_ResultCoercion
import PV_L1_FixedEvents
import PV_L1_Projection
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace MODULE
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged PV_L1_FixedEvents
variable [ExternalTypes] [ExternalFuns]
'''
proof='''  repeat' first
    | apply bind_lift
      intro value
    | apply bind_observe
      intro value
    | exact fixed_lift _
    | exact fixed_pure _
    | split <;> simp only [PV_L1_Projection.prod_case]
'''
for is_absorb in [True,False]:
 n='host_transcript.Transcript.'+('absorb' if is_absorb else 'queries');mod='PV_L1_QueryAbsorb' if is_absorb else 'PV_L1_QueryProducer';raw,params,ret,body=source(n);body,count=instrument(body,0 if is_absorb else 1,is_absorb);assert count==(1 if is_absorb else 16)
 code=base.replace('MODULE',mod)
 if not is_absorb:code='import PV_L1_QueryAbsorb\nimport PV_L1_FixedBind\n'+code
 code+='def produce'+params+ret+'\n  := do\n'+body+'\n\n'
 args='aspis_coredigestDigest32Inst self row payload';theorem_params=params.rstrip().removesuffix(':').rstrip()
 code+='theorem complete_result'+theorem_params+' :\n  erase (produce '+args+') = '+n+' '+args+' := by\n  unfold produce\n  conv_rhs => unfold '+n+'\n'
 simp='simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,Aeneas.Std.bind_tc_ok,PV_L1_Projection.prod_case'+('' if is_absorb else ',PV_L1_QueryAbsorb.complete_result')+']'
 code+='  '+simp+'\n  repeat\' first\n    | with_reducible rfl\n    | split <;> '+simp+'\n    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr\n      intro value called\n#print axioms complete_result\n\n'
 order='[R1Z.SideChannelL1AttemptRecord.Event.call .queryScan 0]' if is_absorb else '(R1Z.SideChannelL1AttemptRecord.Event.call .queryScan 0 :: (List.range 16).map (fun n => .call .queryScan (n+1)))'
 code+='def readOrder : List R1Z.SideChannelL1AttemptRecord.Event := '+order+'\n\n'
 code+='theorem completed_order'+theorem_params+' :\n  Fixed readOrder (produce '+args+') := by\n  unfold produce readOrder\n'
 if not is_absorb:
  code+='  apply PV_L1_FixedBind.bind_fixed _ _ [.call .queryScan 0] ((List.range 16).map (fun n => .call .queryScan (n+1)))\n  · exact PV_L1_QueryAbsorb.completed_order _ _ _ _\n  · intro firstState\n'
  code+='    simp only [PV_L1_Projection.prod_case]\n'+''.join('  '+line+'\n' for line in proof.rstrip().splitlines())
 else:code+=proof
 if not is_absorb:
  code+='    all_goals\n      cases value <;> simp only [List.map_nil,PV_L1_Projection.prod_case]\n      all_goals\n        apply bind_lift\n        intro outcome\n        exact fixed_pure _\n'
 code+='#print axioms completed_order\nend '+mod+'\n';(D/(mod+'.lean')).write_text(code)
(E/'query-instrumentation.json').write_text(json.dumps(dict(source_function='host_transcript.Transcript.queries',digest_reads=17,absorb_reads=1,pair_reads=16,indices=list(range(17)),native_association='V163/V167 retained; no native/differential credit'),indent=2)+'\n')
print('Query producer: one absorb read and sixteen eager block/advance reads')
