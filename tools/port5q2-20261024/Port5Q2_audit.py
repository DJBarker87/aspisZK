#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/port5q2-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
base=subprocess.check_output(['git','rev-parse','034171d163^'],cwd=R,text=True).strip()
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
lean=[json.loads(p.read_text()) for p in sorted(E.glob('lean-*/receipt.json'))]
assert len(lean)<=100
assert not list(E.glob('kani-*/receipt.json'))
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for p in E.glob('*/receipt.json'):
 r=json.loads(p.read_text());assert r['limits']==limits,p
 assert r['swaps']=='0',p
 for name,digest in r['source_hashes'].items():assert sha(p.parent/'sources'/name)==digest,p
 if r['kind']=='lean' and r['exit_status']==0:
  assert not any(a in '\n'.join(r['print_axioms']) for a in ['sorryAx','Lean.ofReduceBool','Lean.trustCompiler']),p
accepted=[];theorems=[]
for src in sorted(L.glob('Port5Q2_*.lean')):
 matches=[r for r in lean if r['exit_status']==0 and r['source_hashes'].get(src.name)==sha(src)]
 assert matches,src
 text=src.read_text();clean=re.sub(r'/-.*?-/', '', text, flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
 assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxHeartbeats|maxRecDepth)\b',clean),src
 for name in re.findall(r'^theorem (\w+)',clean,re.M):
  ns=re.search(r'^namespace (\S+)',clean,re.M).group(1);theorems.append(ns+'.'+name)
 accepted.append({'module':src.stem,'sha256':sha(src),'receipt':matches[-1]['attempt']})
final=next(r for r in reversed(lean) if r['exit_status']==0 and 'Port5Q2_Audit.lean' in r['source_hashes'])
for theorem in theorems:assert any("'"+theorem+"' " in line for line in final['print_axioms']),theorem
changes=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
allowed=('evidence/port5q2-20261024/','tools/port5q2-20261024/','docs/research/100bit-spend-path-20261013/lean/Port5Q2_')
assert all(p.startswith(allowed) for p in changes),[p for p in changes if not p.startswith(allowed)]
writer=json.loads((E/'writer-admission.json').read_text())
for name,digest in writer['current_source_snapshot_pins'].items():assert sha(R/name)==digest,name
for name in ['raw','scalar','semantic','validate','weights']:
 x=json.loads((E/(name+'-emission.json')).read_text());assert x['source_sha256']==sha(E/'reader-helpers/Funs.lean'),name
 module={'raw':'ReaderRaw','scalar':'ReaderScalar','semantic':'ReaderSemantic','validate':'ReaderValidate','weights':'ReaderWeights'}[name]
 assert x['module_sha256']==sha(L/('Port5Q2_'+module+'.lean')),name
 assert not x['external_template_imported']
manifest={'schema':'focused-extractor-proof-packet-v1','job':'port5q2-20261024','branch':'codex/cx-port5q2-20261024','baseline_revision':base,'source_revision':revision,'accepted_modules':accepted,'final_top_theorems':theorems,'final_audit':final,'actual_lean_compiles':len(lean),'lean_budget':100,'new_kani_runs':0,'kani_budget':60,'excluded_attempts':[r['attempt'] for r in lean if r['exit_status']!=0],'caps':limits,'validation':'Focused individual modules and one compatible-import/axioms union audit. Existing native writer/codec certificates reused, not replayed. No frozen-manifest or runtime suite rerun.','scope':'Same-prefix raw canonicality and conditional ten-step/checkpoint rows; current raw/scalar/semantic/validator/weight helper transports. Concrete Session A prepare/primitive instances, frozen2 immutable Prepared and observed value/basis binding, contextual native op18/codec/runtime/P6/source-to-ELF installation remain open. No S2 release claim.','source_change_assessment':'New prefixed proof modules and evidence/tools only. No shipped/existing module, feature, protocol/wire parameter, key, or other worktree change. ELF rebuild trigger did not fire.','inherited_elf_pins':['f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548']}
(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'status':'PASS','modules':len(accepted),'top_axiom_audits':len(theorems),'lean_attempts':len(lean),'new_kani_runs':0,'shipped_delta':[]}))
