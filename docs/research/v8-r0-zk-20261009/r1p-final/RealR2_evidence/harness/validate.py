from pathlib import Path
import sys,json,hashlib,re,subprocess
assert sys.argv[1:]==['--check']
E=Path(__file__).resolve().parent.parent
R=Path(__file__).resolve().parents[6]
L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
accepted={'RealR2_SeedGuard':11006,'RealR2_Context':11008,'RealR2_Seed':11010,'RealR2_SeedImage':11011,'RealR2_Audit':11012}
for name,a in accepted.items():
 p=L/(name+'.lean');s=p.read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option max(?:RecDepth|Heartbeats)',s),name
 receipt=json.loads((E/'lean'/str(a)/'evidence.json').read_text())
 assert receipt['exit_status']==0 and receipt['swaps']==0,receipt
 assert hashlib.sha256(p.read_bytes()).hexdigest()==receipt['source_sha256'],name
 assert not any('sorryAx' in l for l in receipt['axioms_lines'])
 for line in receipt['axioms_lines']:
  assert set(re.search(r'axioms: \[(.*)\]',line)[1].split(', '))<={'propext','Classical.choice','Quot.sound',''}
 audit=receipt if name=='RealR2_Audit' else None
assert len(json.loads((E/'lean/11012/evidence.json').read_text())['axioms_lines'])==6
base=json.loads((E/'source-pins.json').read_text())['revision']
changed=subprocess.check_output(['git','diff','--name-only',base,'--','crates','programs'],text=True)
assert not changed,changed
files=subprocess.check_output(['git','ls-tree','-r','--name-only',base,'--','crates','programs'],text=True).splitlines()
assert all(subprocess.check_output(['git','show',base+':'+p])==(R/p).read_bytes() for p in files)
unknown=subprocess.check_output(['git','ls-files','--others','--exclude-standard','--','crates','programs'],text=True)
assert not unknown,unknown
for n in ['RealR2_context_v1','RealR2_seed_v1']:
 receipt=json.loads((E/'native-receipts'/n/'receipt.json').read_text());assert receipt['exit_status']==0
 for path,sha in json.loads((E/(n+'-inputs.json')).read_text()).items():
  assert hashlib.sha256((E/path).read_bytes()).hexdigest()==sha,path
n='RealR2_scalar_contract_v1';receipt=json.loads((E/'native-receipts'/n/'receipt.json').read_text());assert receipt['exit_status']==124
for path,sha in json.loads((E/(n+'-inputs.json')).read_text()).items():
 assert hashlib.sha256((E/path).read_bytes()).hexdigest()==sha,path
r=dict(accepted=accepted,theorems_audited=6,shipped_files_unchanged=len(files),no_untracked_shipped_files=True,kani_passed=2,kani_timed_out=1,real_refinement_established=False)
(E/'validation.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
