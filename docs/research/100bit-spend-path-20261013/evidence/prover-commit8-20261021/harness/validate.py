#!/usr/bin/env python3
"""Validate immutable receipt/source identities without replaying a build."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent.parent
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
rows=[]
for p in sorted((E/'lean').glob('lean-*.json')):
 x=json.loads(p.read_text());a=x['attempt'];name=Path(x['module']).stem
 src=E/'lean'/'sources'/f'attempt-{a}-{name}.lean.txt'
 assert src.exists() and sha(src)==x['source_sha256'],(a,src)
 out=(E/'lean'/f'out-{a}.log').read_text();tm=(E/'lean'/f'time-{a}.log').read_text()
 status=int(re.search(r'^exit=(\d+)',out,re.M)[1]);audits=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",out,re.S)
 if status==0:
  for theorem,axs in audits:assert set(re.findall(r'[A-Za-z_.]+',axs))<=allowed,(a,theorem,axs)
  assert not re.search(r'\berror:',out)
 rows.append(dict(attempt=a,module=x['module'],exit_status=status,source_sha256=x['source_sha256'],deps_fingerprint=x['deps_fingerprint'],source_base_revision=x.get('source_base_revision','a9a27745b'),wall_time=re.search(r'Elapsed.*: (.+)',tm)[1],peak_rss_kib=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',tm)[1]),swaps=int(re.search(r'Swaps: (\d+)',tm)[1]),axioms=[dict(theorem=t,axioms=re.findall(r'[A-Za-z_.]+',a)) for t,a in audits],accepted=status==0))
(E/'lean'/'attempts-all.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
accepted=['scalar-step-v1','mask-four-trace-v3','source-four-trace-v3','balance-m31-step-v3','balance-qm31-step-v3']
for name in accepted:
 p=E/'receipts'/name;r=json.loads((p/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0
 assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 assert 'VERIFICATION:- SUCCESSFUL' in (p/'stdout.log').read_text()
 assert r['env']['RUSTFLAGS']=='-C link-arg=-Wl,--threads=4'
for row in json.loads((E/'rust-source-map.json').read_text()):assert sha(Path(row['matching_file']))==row['sha256']
elf=json.loads((E/'frozen-elf-final-check.json').read_text())
for mode,r in elf['programs'].items():assert r['cmp_exit']==0 and r['byte_identical'] and r['sha256']==r['expected_sha256'] and r['receipt']['exit_status']==0 and r['receipt']['swaps']==0
x=json.loads((E/'checklist-deletion-audit.json').read_text());assert x['before']==x['after'] and x['deletions']==[]
assert x['before_sha256']==x['after_sha256']==sha(Path(x['endpoint_path']))
assert (E/'checklist-deletions.diff').read_bytes()==b''
assert json.loads((E/'step-llbc-v3.json').read_text())['has_errors'] is False
raw=json.loads((E/'extraction'/'artifact-identities.json').read_text())
f=next(x for x in raw if x['path'].endswith('/Funs.lean'))
assert f['sha256']==sha(Path('docs/research/v8-r0-zk-20261009/lean/AspisR1ProverStep8/Funs.lean'))
# Current declarations must all appear in the latest coherent accepted audit.
final=max((r for r in rows if r['accepted'] and r['module'].endswith('Audit.lean')),key=lambda r:r['attempt'])
names={r['theorem'] for r in final['axioms']}
for name in ['ProverCommitStepLoop','ProverCommitFourSteps','ProverCommitFoldSteps','ProverCommitCallerObstruction','ProverCommitReferenceReads','PrivacyR1FinalProtocolCallerScope']:
 text=Path('docs/research/v8-r0-zk-20261009/lean/R1Z',name+'.lean').read_text()
 for theorem in re.findall(r'^theorem (\w+)',text,re.M):assert 'R1Z.'+name+'.'+theorem in names,(name,theorem)
tracked=subprocess.check_output(['git','diff','--name-only','a9a27745b'],text=True).splitlines()
assert not any(p.endswith(('.olean','.so','.tar.gz','.llbc')) for p in tracked)
result=dict(attempts=len(rows),accepted_lean_attempts=sum(r['accepted'] for r in rows),final_audit=final['attempt'],final_axioms_lines=len(final['axioms']),accepted_kani_targets=len(accepted),rust_source_identities=len(json.loads((E/'rust-source-map.json').read_text())),elf_comparisons=len(elf['programs']),checklist_deletions=0)
(E/'validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
