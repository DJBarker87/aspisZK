"""Validate owned evidence integrity; no prover launch or shared-state mutation."""
from pathlib import Path
import json,hashlib,lzma,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(p):
 if p.is_file():return p.read_bytes()
 if p.with_name(p.name+'.xz').is_file():
  raw=lzma.decompress(p.with_name(p.name+'.xz').read_bytes())
  assert sha(raw)==p.with_name(p.name+'.sha256').read_text().strip(),str(p)
  return raw
 ref=json.loads(p.with_name(p.name+'.ref.json').read_text());raw=(E/ref['owned_input']).read_bytes()
 if ref.get('compression')=='xz':raw=lzma.decompress(raw)
 assert sha(raw)==ref['sha256'],str(p)
 return raw
attempts=[json.loads(s) for s in (E/'NLL_ATTEMPTS.jsonl').read_text().splitlines() if s]
assert len({a['attempt'] for a in attempts})==len(attempts)
assert sum(a['kind']=='kani' for a in attempts)<=40
assert sum(a['kind']!='kani' for a in attempts)<=140
assert sum(a['kind']=='audit' for a in attempts)<=2
snapshots=0
for a in attempts:
 r=json.loads((E/a['full_receipt']).read_text());assert r['attempt']==a['attempt']
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['env']['CARGO_TARGET_DIR']=='/home/dombarker/project-offloads/codex-cx-batch-merkle5-20261110/NLL_target'
 assert int(r['swaps'])==0
 admission=json.loads((E/(a['attempt']+'-admission.json')).read_text())
 assert admission['exit']==0 and admission['reservation']['allowed'] is True
 assert admission['reservation']['NLL_resource_preflight']['free_bytes']>=40000000000
 if r['kind']=='lean':assert '-M7000' in r['command']
 for name,wanted in r['source_hashes'].items():
  assert sha(read(E/a['attempt']/'sources'/name))==wanted,(a['attempt'],name)
  snapshots+=1
selected=json.loads((E/'NLL_PROOF_SET.json').read_text())
for module,pin in selected.items():
 assert module.startswith('NLL_')
 for name,wanted in pin['source_hashes'].items():assert sha((E/name).read_bytes())==wanted,name
 for line in pin['print_axioms']:
  assert 'sorryAx' not in line,line
  hit=re.search(r'depends on axioms: \[([^]]*)\]',line)
  if hit:assert {x.strip() for x in hit[1].split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'}
for p in E.glob('NLL_*.lean'):
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b|set_option\s+(maxRecDepth|maxHeartbeats)',p.read_text(),re.M),p.name
for p in E.rglob('*'):
 if p.is_file():
  assert p.stat().st_size<=20000000,p
  assert p.suffix not in {'.olean','.ir','.o','.a','.so','.elf','.dylib','.pyc'},p
assert json.loads((E/'NLL_CLOSED.json').read_text())['closed_rows']==[]
assert json.loads((E/'NLL_LEDGER_DELTA.json').read_text())['promotions']==[]
for filename in ['NLL_REUSED_PINS.json','NLL_INPUTS.json']:
 for name,pin in json.loads((E/filename).read_text()).items():assert sha(Path(name).read_bytes())==pin['sha256'],name
result={'integrity':'PASS','scopes':len(attempts),'source_snapshots_checked':snapshots,'new_modules':len(selected),'kani':sum(a['kind']=='kani' for a in attempts),'lean':sum(a['kind']=='lean' for a in attempts),'link':sum(a['kind']=='link' for a in attempts),'audit':sum(a['kind']=='audit' for a in attempts),'extraction':0,'security_target_established':False}
if (E/'NLL_AX2_RESULT.json').exists():
 ax=json.loads((E/'NLL_AX2_RESULT.json').read_text());scan=json.loads((E/'NLL_NFX_RESULT.json').read_text())
 assert ax['exit_status']==0 and ax['all_equal'] and ax['all_standard_axioms']
 assert scan['exit_status']==0 and scan['dangling']==scan['duplicate_owners']==scan['imports_mismatch']==0
 result['combined_audit']='PASS'
 if (E/'NLL_CLOSURE_PINS.json.xz').exists():
  raw=lzma.decompress((E/'NLL_CLOSURE_PINS.json.xz').read_bytes())
  assert sha(raw)==(E/'NLL_CLOSURE_PINS.json.sha256').read_text().strip()
  post=json.loads(raw)['selected']
  before=json.loads((E/'NLL_L072/receipt.json').read_text())['deps_fingerprint']['selected_objects']
  library={p:v for p,v in before.items() if '/Aeneas/' in p or '/AeneasMeta/' in p or Path(p).name.startswith(('Aeneas.','AeneasMeta.'))}
  assert library
  for p,v in library.items():assert p in post and post[p]['sha256']==v['sha256'],p
  result['Aeneas_objects_unchanged']=len(library)
  result['closure_objects']=len(post)

(E/'NLL_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
