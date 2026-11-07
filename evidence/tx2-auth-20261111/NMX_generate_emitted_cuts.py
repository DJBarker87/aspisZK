"""Factor the retained ACTUAL emitted body into exact source-order CPS tails.
No child body is unfolded. Local per-call proofs compare the accepted source
value folds to these literal emitted tails, instead of normalizing a whole run.
"""
from pathlib import Path
import re,json
E=Path(__file__).resolve().parent
ctx={'__file__':str(E/'NMX_generate_steps.py')};exec((E/'NMX_generate_steps.py').read_text().split('manifest=[]')[0],ctx)
types=ctx['types'];plan=json.loads((E/'NMX_FOLD_PLAN.json').read_text())
text=(E/'NMX_Emitted.lean').read_text();text=text[text.index('  := do')+8:text.index('\nend NMX_Emitted')]
renames={
'verifier_program':'verifier','pool_program':'pool','output_lane':'outputLane','current_slot':'slot',
'proof_account':'proof','master_account':'masterAccount','checkpoint_account':'checkpointAccount',
'lane_account':'laneAccount','registry_account':'registryAccount','entry_account':'entryAccount','verifier_checkpoint':'verifierCheckpoint',
'val':'masterBytes','val1':'master','val2':'derivedMaster','val3':'checkpointBytes','val4':'checkpoint',
'val5':'derivedCheckpoint','val6':'laneBytes','val7':'lane','val8':'derivedLane',
'p':'masterKey','p1':'mintKey','p2':'checkpointKey','p3':'laneKey','a':'masterKeyBytes','a1':'checkpointMasterBytes',
'a2':'sequenceBytes','a3':'laneMasterBytes','a4':'snapshotPool','a5':'returnedMasterBytes','a6':'returnedCheckpointBytes','a7':'returnedLaneBytes',
'b':'wrongMaster','b1':'wrongMasterPda','b2':'wrongCheckpointMaster','b3':'wrongDeployment','b4':'wrongCheckpointPda','b5':'wrongLaneMaster','b6':'wrongLanePda',
'i1':'allLanes','s':'mintSeed','s1':'bumpSeed','s2':'masterSeeds','s3':'checkpointMasterSeed','s4':'sequenceSeed','s5':'checkpointBump','s6':'checkpointSeeds',
's7':'laneMasterSeed','s8':'laneIdSeed','s9':'laneBump','s10':'laneSeeds'}
# Rename identifiers only, NEVER structure field labels or projections.
def rename(m):
 n=m[0];pos=m.start();end=m.end()
 if pos and text[pos-1]=='.':return n
 if re.match(r'\s*:=',text[end:]):
  # let-local names followed := are renamed; record labels are not.
  prev=text[max(0,pos-8):pos]
  if not re.search(r'\blet\s+$',prev):return n
 return renames.get(n,n)
text=re.sub(r'\b[A-Za-z_][A-Za-z_0-9]*\b',rename,text)
text=re.sub(r'\blaneCall\b','ops.op50',text)
text=re.sub(r'\bregistryCall\b','(r1_pool_adapter.owned.authenticate_invariant_release_registry ops)',text)
lines=text.splitlines();indent=lambda line:len(line)-len(line.lstrip())
patterns=[
'let proof ←','let masterAccount ←','let checkpointAccount ←','let laneAccount ←','let registryAccount ←','let entryAccount ←','let verifierCheckpoint ←',
'let r ←','let r1 ←','let r2 ←','let r3 ←','let r4 ←','let r5 ←','let r6 ←','let r7 ←','let masterKey ←','let masterKeyBytes ←','let wrongMaster ←','if wrongMaster',
'let allLanes ←','if master.initialized_lane_mask','let mintKey ←','let mintSeed ←','let r8 ←','let wrongMasterPda ←','if wrongMasterPda','let r10 ←','let r11 ←','let r12 ←',
'let checkpointMasterBytes ←','let wrongCheckpointMaster ←','if wrongCheckpointMaster','let wrongDeployment ←','if wrongDeployment','let checkpointMasterSeed ←','let r13 ←','let checkpointKey ←',
'let wrongCheckpointPda ←','if wrongCheckpointPda','let r15 ←','let r16 ←','let laneMasterBytes ←','let wrongLaneMaster ←','if wrongLaneMaster','if lane.lane_id',
'let laneMasterSeed ←','let r17 ←','let laneKey ←','let wrongLanePda ←','if wrongLanePda','let snapshotPool ←',None,'let returnedMasterBytes ←','let returnedCheckpointBytes ←','let returnedLaneBytes ←']
assert len(patterns)==55
starts=[];ends=[]
for pat in patterns:
 if pat is None:starts.append(None);ends.append(None);continue
 matches=[i for i,l in enumerate(lines) if re.match(re.escape(pat)+r'(?=$|\W)',l.strip())]
 assert len(matches)==1,(pat,matches)
 i=matches[0];start=indent(lines[i]);j=i+1
 while j<len(lines) and (not lines[j].strip() or indent(lines[j])>=start):j+=1
 starts.append(i);ends.append(j)
# The extraction erases the final allocation; expose its pure payload value
# at the existing source position, without inventing any value effect.
last='\n'.join(lines[starts[54]:ends[54]])
a=last.index('live_snapshot :=');b=last.index('frontier :=',a);c=last.index('}',b)
payload=last[last.index('{',a):c+1]
# Normalize its indent; this literal is reused at the synthetic pure52 cut.
payload='\n'.join(l.strip() for l in payload.splitlines())
rawtype=dict(types);rawtype.update(master='Master',checkpoint='Checkpoint',lane='Lane',live='Snapshot')
files=[]
for group in range(6):
 lo=10*group+1;hi=min(10*(group+1),55);module=f'NMX_Actual{group:02d}'
 imports=['NMX_ResultSteps']+([f'NMX_Actual{group+1:02d}'] if hi<55 else [])
 out='\n'.join('import '+m for m in imports)+f'''\nset_option autoImplicit false
noncomputable section
namespace {module}
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_ResultSteps
'''
 for i in range(hi,lo-1,-1):
  st=plan[i-1];params=' '.join(f'({n} : {rawtype[n]})' for n in st['params'])
  if i==52:
   ns='NMX_Actual05';args=' '.join(plan[52]['params']);body=f'let live : Snapshot := {payload}\n{ns}.t053 owners {args}'
  else:
   start=starts[i-1];end=ends[i-1];region=list(lines[start:end]);base=indent(lines[start])
   if i<55:
    ni=52 if i==51 else i+1;replace_i=53 if ni==52 else ni
    nstart=starts[replace_i-1];nend=ends[replace_i-1];assert start<=nstart<nend<=end,(i,start,nstart,nend,end)
    ns=f'NMX_Actual{(ni-1)//10:02d}';args=' '.join(plan[ni-1]['params'])
    region[nstart-start:nend-start]=[' '*indent(lines[nstart])+f'{ns}.t{ni:03d} owners {args}']
   body='\n'.join(l[base:] for l in region)
   if i==55:
    ia=body.index('live_snapshot :=');ib=body.index('frontier :=',ia);ic=body.index('}',ib)
    body=body[:ia]+'live_snapshot := live'+body[ic+1:]
  out+=f'\ndef t{i:03d} (owners : Owners) {params} : Final := do\n'+ '\n'.join('  '+l for l in body.splitlines())+'\n'
 out+=f'end {module}\nend\n';(E/(module+'.lean')).write_text(out);files.append(module)
(E/'NMX_ACTUAL_CUTS.json').write_text(json.dumps(dict(source='NMX_Emitted.lean',files=files,starts=starts,ends=ends,renames=renames,synthetic52='pure live-snapshot payload factor only; allocation erased by extraction'),indent=1)+'\n')
print('Factored55 emitted value cuts in6 modules; no theorem/credit claimed.')
