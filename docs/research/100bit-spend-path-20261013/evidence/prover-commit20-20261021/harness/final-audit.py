"""Audit this packet without rerunning unchanged compiler or runtime suites."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent.parent
ROOT=Path.cwd();BASE='8f5d893d7'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows=[]
for p in sorted((E/'lean').glob('attempts-*.jsonl')):
 rows += [json.loads(line) for line in p.read_text().splitlines()]
assert len({x['attempt'] for x in rows})==len(rows)
for x in rows:
 assert 8705<=x['attempt']<=8799
 snapshots=list((E/'lean/sources').glob('attempt-'+str(x['attempt'])+'-*.lean.txt'))
 assert len(snapshots)==1 and sha(snapshots[0])==x['source_sha256'],x['attempt']
 assert x['swaps']==0 and x['deps_fingerprint'] and x['source_revision']
 if x['accepted']:assert not x['errors'] and all('sorryAx' not in a for a in x['axioms'])
audit=next(x for x in rows if x['attempt']==8732);assert audit['exit_status']==0
allowed={'propext','Classical.choice','Quot.sound'}
for ax in audit['axioms']:
 if 'depends on axioms:' in ax:
  names=ax.split('[')[1].split(']')[0].replace('\n','').split(',')
  assert set(n.strip() for n in names)<=allowed,ax
proofs=['ProverCommitTable20','ProverCommitFields20','ProverCommitSemantic20','ProverCommitTableHistory20','ProverCommitNonzero20']
for m in proofs:
 p=ROOT/'docs/research/v8-r0-zk-20261009/lean/R1Z'/(m+'.lean');s=p.read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',s),p
 for n in re.findall(r'^theorem (\w+)',s,re.M):
  assert any("'R1Z."+m+'.'+n+"'" in a for a in audit['axioms']),n
for folder,d in [('fields-owned-v2','AspisR1SimFields20'),('semantic-owned-v1','AspisR1SimSemantic20')]:
 p=E/'extraction'/folder
 for x in json.loads((p/'promotion.json').read_text())['files']:
  assert sha(p/(x['file']+'.txt'))==x['raw_sha256']
  assert sha(ROOT/'docs/research/v8-r0-zk-20261009/lean'/d/x['file'])==x['promoted_sha256']
  assert not re.search(r'^axiom ',(ROOT/'docs/research/v8-r0-zk-20261009/lean'/d/x['file']).read_text(),re.M)
changed=subprocess.check_output(['git','diff',BASE,'--name-only'],text=True).splitlines()
assert not any(p.startswith(('crates/','programs/')) for p in changed)
assert not any(any(q in p for q in ['SourceIdentification','RustRuntimeJoin','PrivacyR1FinalRelease']) for p in changed)
assert not any(p.endswith(('.olean','.elf','.so','.llbc','.tar','.gz')) for p in changed)
endpoint='docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployed.lean'
assert subprocess.check_output(['git','show',BASE+':'+endpoint])==Path(endpoint).read_bytes()
rust=json.loads((E/'rust-attempts.json').read_text())
for x in rust:
 assert x['swaps']==0
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 if x['accepted']:
  assert x['exit_status']==0
  if x['name']=='semantic-runtime-v2':
   assert 'test result: ok. 2 passed' in (E/'receipts'/x['name']/'stdout.log').read_text()
  elif not x['name'].startswith(('sim-fields-owned-v2-','sim-semantic-owned-v1-')):
   assert 'VERIFICATION:- SUCCESSFUL' in (E/'receipts'/x['name']/'stdout.log').read_text()
result=dict(base_revision=BASE,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 packet_valid=True,formal_target_established=False,lean_attempts=len(rows),retired_attempts=[8713,8714],
 final_audit={k:audit[k] for k in ['module','attempt','source_sha256','deps_fingerprint','source_revision','exit_status','wall_time','peak_rss_kib','swaps','axioms']},
 accepted_rust=[x['name'] for x in rust if x['accepted']],
 endpoint_sha256=sha(endpoint),endpoint_unchanged=True,shipped_sources_unchanged=True,
 frozen_ELFs='Unchanged shipped sources: reuse D129 three-ELF byte-identical evidence at base; no new rebuild claimed.',
 remaining=['universal BTreeMap/owned Vec source transport including arbitrary key lengths',
 'production iterator/control/caller join for owned semantic rows and compact/logical carrier',
 'rows 25-32 and full opening/programming/serialization/error/retry source joins',
 'uncapped nonzero loop treatment and actual randomness/history law',
 'concrete shippedProverExperiment and both WholeRunJoins'],
 release_replay='not run: full dependency/source closure is not green; final audit uses cached accepted cone')
(E/'final-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['packet_valid','formal_target_established','lean_attempts','shipped_sources_unchanged','endpoint_unchanged']}))
