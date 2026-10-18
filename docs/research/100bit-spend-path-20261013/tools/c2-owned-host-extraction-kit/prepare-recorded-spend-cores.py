#!/usr/bin/env python3
"""Stage six exact spend definition cores and a source/producer inverse audit.
No Lean is invoked. Elaboration is an explicitly separate acceptance step.
"""
from pathlib import Path
import argparse,gzip,hashlib,importlib.util,json,re
ROOT=Path(__file__).resolve().parents[5];B=ROOT/'docs/research/100bit-spend-path-20261013';E=B/'evidence/c2-recorded-current-audit-20261018';OUT=B/'lean/recorded-current-cores-20261018'
sha=lambda b:hashlib.sha256(b).hexdigest()
def load(n,p):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
PLAN=[
 ('AspisFormal.Pool.V7PairLeafOccupancy','R1PairLeafOccupancyCore',['Mathlib.Tactic']),
 ('R1InputWitnessCore','R1InputWitnessRelationCore',['R1PairLeafOccupancyCore','R0P.Semantics']),
 ('R1AppendNode','R1AppendFrozenCore',['R0P.EmptyRoots']),
 ('R1AppendPath','R1AppendPathCore',['R1AppendFrozenCore','R0P.Digest','R0P.Semantics']),
 ('R1SpendAppendBinding','R1SpendAppendBindingCore',['R1AppendPathCore','R0P.Core']),
 ('R1SpendRelation','R1SpendRelationCore',['R1InputWitnessRelationCore','R1SpendAppendBindingCore','PublicOptionShape','AspisV8R15.ExactTowerBase'])]
def main():
 a=argparse.ArgumentParser();a.add_argument('--snapshot',type=Path,required=True);a.add_argument('--check',action='store_true');args=a.parse_args()
 snapshot=args.snapshot.read_bytes();assert sha(snapshot)=='a5a1661e0da6a4295714eb80b57b80ae9a5d7e00f5b6c75cdf83c2d92af45a2c';pin=json.loads(snapshot)
 inv=load('inventory',B/'tools/j1-integrated-declaration-repin.py');parser=load('parser',Path(__file__).with_name('model-command-parser.py'));use=load('use',Path(__file__).with_name('audit-recorded-definition-use.py'))
 g=json.loads(gzip.decompress((E/'candidate-closure.json.gz').read_bytes()));audit={'classification':'STAGED_EXACT_DEFINITION_CORE_SPLIT_PENDING_ELABORATION','source_revision':g['git_revision'],'base_snapshot_sha256':sha(snapshot),'base_snapshot_modules':len(pin['modules']),'source_commands':19,'targets':[],'new_Lean_jobs':0,'elaboration_status':'PENDING: exact implicit/typeclass signatures and auxiliary declarations must be inspected after focused compilation.'}
 staged=set();boundaries={}
 for old,new,imports in PLAN:
  node=g['fresh_sources'][old];source=node['source'];raw=source.encode();ds=parser.commands(source,inv.lean_tokens,inv.canonical);wanted=use.SPEND[old];cut=[]
  for key,d in ds.items():
   if key not in wanted:cut.append((d['start_byte'],d['end_byte_exclusive']))
  for start,end in sorted(cut,reverse=True):raw=raw[:start]+raw[end:]
  text=raw.decode();text=re.sub(r'^import .*\n','',text,flags=re.M);text=re.sub(r'^#print axioms .*\n','',text,flags=re.M)
  text=''.join('import '+m+'\n' for m in imports)+'\n'+text.lstrip('\n')
  # Print elaborated signatures, generated structure fields and axiom dependencies.
  trailer='\nset_option pp.universes true in\n#check @'+ds[wanted[0]]['qualified_name']+'\n'
  for key in wanted:
   name=ds[key]['qualified_name'];trailer+='\n#print '+name+'\n#print axioms '+name+'\n'
  text+='\n'+trailer
  fresh=parser.commands(text,inv.lean_tokens,inv.canonical);assert set(fresh)==set(wanted),(old,set(fresh),wanted)
  pairs=[]
  for key in wanted:
   before,after=ds[key],fresh[key]
   for field in ['qualified_name','kind','declaration_token_sha256','signature_token_sha256','signature_tokens','active_scope_syntax','context_command_history_sha256','immediately_preceding_transient_context']:
    assert before[field]==after[field],(old,key,field)
   assert [c['tokens'] for c in before['context_command_history']]==[c['tokens'] for c in after['context_command_history']],(old,key,'context syntax')
   pairs.append({'source_selector':key,'original_command':before,'staged_command':after})
  for m in imports:
   if m in staged:continue
   assert m in pin['modules'],('unsupported import',m)
   boundaries[m]=pin['modules'][m]
  path=OUT/(new+'.lean')
  if args.check:assert path.read_text()==text,path
  else:path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
  audit['targets'].append({'module':new,'source_path':str(path.relative_to(ROOT)),'source_sha256':sha(text.encode()),'imports':imports,'original_source_module':old,'original_source_path':node['path'],'original_source_sha256':node['source_sha256'],'original_imports':node['imports'],'exact_selected_commands':pairs,'excluded_commands':[k for k in ds if k not in wanted],'binding_audit':'Exact command/signature/context tokens only; imported boundary source/object/producer identity pinned; generated/inferred elaboration not yet accepted.'});staged.add(new)
 # Enumerate full boundary closure, reject historical RawCut/spend modules and missing nodes.
 closure={};todo=list(boundaries)
 while todo:
  m=todo.pop()
  if m in closure:continue
  n=pin['modules'][m];closure[m]=n
  assert not m.startswith(('RawCut','C2OwnedHost','C2RecordedExperiment')),m
  assert m not in {x[0] for x in PLAN},('would duplicate original declaration provider',m)
  for d in n['imports']:
   assert d in pin['modules'],('missing snapshot dependency',m,d)
   todo.append(d)
 audit['external_direct_boundaries']=boundaries;audit['external_transitive_module_count']=len(closure);audit['external_transitive_identity_sha256']=sha(json.dumps(closure,sort_keys=True,separators=(',',':')).encode())
 audit['resource_plan']={'targets':6,'command':'lake env lean -o <fresh-object> <exact-source>','MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'host_shared_lock':'/tmp/aspis-r0-lean.lock','guard':'Atomic external-Lean preflight and continuous guard; stop only own process on conflict.','scope':'One focused target at a time, no dependency build, no historical13 objects.'}
 report=(json.dumps(audit,sort_keys=True,indent=2)+'\n').encode();dest=OUT/'source-inverse-preflight.json'
 if args.check:assert dest.read_bytes()==report,'audit mismatch'
 else:dest.write_bytes(report)
 print(json.dumps({'status':'PASS_STAGING_INVERSE_ONLY','targets':6,'source_commands':19,'direct_current_boundaries':len(boundaries),'transitive_current_modules':len(closure),'report_sha256':sha(report),'elaboration':'PENDING','new_Lean_jobs':0},sort_keys=True))
if __name__=='__main__':main()
