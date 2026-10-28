from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l1-20261028';D=R/'docs/research/v8-r0-zk-20261009/lean'
s=json.loads((E/'focused-project-sources.json').read_text())['R1Z.ProverRwFullFuns'];n='host_transcript.Transcript.queries';a=s.index('def '+n+'\n');b=s.index('\n/--',a);raw=s[a:b];h,body=raw.split('\n  := do\n',1);sig=h[len('def '+n):];pos=sig.rfind('\n  Result');params=sig[:pos];ret=sig[pos:].replace('\n  Result','\n  Logged',1)
lines=body.splitlines();digest=[]
for at in reversed(range(len(lines))):
 line=lines[at]
 if '←' not in line or not re.match(r'\s*let\b',line):continue
 indent=len(line)-len(line.lstrip());end=at+1
 while end<len(lines) and (not lines[end].strip() or len(lines[end])-len(lines[end].lstrip())>indent):end+=1
 prefix,first=line.split('←',1);expr='\n'.join([first.strip()]+lines[at+1:end]).strip()
 if expr.startswith('aspis_coredigestDigest32Inst.digest '):digest.append(at)
 lines[at:end]=[prefix+'← PV_L1_Logged.lift ('+expr+')']
body='\n'.join(lines);k=0
# The exact sixteen emitted calls, in source order; absorption is a separate
# native helper and is deliberately not counted as a block/advance pair read.
pat=r'PV_L1_Logged.lift \((aspis_coredigestDigest32Inst\.digest [^\n]*)\)'
def mark(m):
 global k
 out='observe .queryScan '+str(k)+' ('+m[1]+')';k+=1;return out
body=re.sub(pat,mark,body);assert k==16,k
body=re.sub(r'(?<![A-Za-z0-9_.])ok(?=\s|\()', 'Pure.pure',body)
code='''import PV_L1_ResultCoercion
import PV_L1_FixedEvents
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_QueryProducer
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged PV_L1_FixedEvents
variable [ExternalTypes] [ExternalFuns]
'''
code+='def produce'+params+ret+'\n  := do\n'+body+'\n\n'
code+='def readOrder : List R1Z.SideChannelL1AttemptRecord.Event :=\n  (List.range 16).map (fun n => .call .queryScan n)\n\n'
code+='theorem completed_order'+params.rstrip().removesuffix(':').rstrip()+' :\n  Fixed readOrder (produce aspis_coredigestDigest32Inst self row payload) := by\n'
code+='  unfold produce readOrder\n  repeat\' first\n    | apply bind_lift\n      intro value\n    | apply bind_observe\n      intro value\n    | exact fixed_lift _\n    | exact fixed_pure _\n    | split\n'
code+='#print axioms completed_order\nend PV_L1_QueryProducer\n'
(D/'PV_L1_QueryProducer.lean').write_text(code)
(E/'query-instrumentation.json').write_text(json.dumps(dict(source_function=n,source_sha256=hashlib.sha256(raw.encode()).hexdigest(),digest_read_count=16,absorb_excluded=True,source_order=list(range(16)),method='literal emitted body with only Logged lifts and call entry markers',native_association='V163/V167 retained; no native/differential credit'),indent=2)+'\n')
print('Query producer: sixteen source digest-read entry markers')
