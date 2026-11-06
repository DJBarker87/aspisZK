"""Strict additive packet validation and denial controls; no proof/build replay."""
from pathlib import Path
import copy,json,hashlib,lzma,subprocess,re
E=Path(__file__).resolve().parent;R=E.parent.parent;H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ids={'TX1:155','TX1:157','TX1:158','TX1:159','TX1:160','TX1:165','TX1:166','TX1:167'}
packet=json.loads((E/'NKD_CLOSED.json').read_text());delta=json.loads((E/'NKD_LEDGER_DELTA.json').read_text());audit=json.loads((E/'NKD_AUDIT.json').read_text());baseline=R/delta['baseline'];base=json.loads(lzma.decompress(baseline.read_bytes()));rs={r['row']:r for r in base['rows']}
assert H(baseline)==delta['baseline_sha256']and base['counts']=={'CLOSED':514,'OPEN':85}
def validate(p):
 assert p['target_established']is False and p['headline']=='AspisR1.RPx_Deployed.deployed'
 assert len(p['functions'])==8 and {f['rows'][0]for f in p['functions']}==ids
 roots=set(json.loads((E/'NKD_AUDIT_ROOTS.json').read_text())['roots'])
 for f in p['functions']:
  row=f['rows'][0];old=rs[row]
  assert f['function']==old['function']and old['status']=='OPEN'
  assert f['baseline_obligation_statement_hash']==old['obligation_statement_hash']
  assert f['frozen_body_sha256']==old['frozen_body_sha256']
  assert f['complete_carrier']is True and f['native_pairs']and f['lean_roots']
  assert set(f['lean_roots'])<=roots
  assert f['status']=='GATED_CANDIDATE_AWAITING_NEXT_LEDGER'
  assert {c['function']for c in f['canonical_callees']}==set(old['canonical_callees'])
  assert all(c['internal_packet']or c['baseline_status']=='CLOSED'for c in f['canonical_callees'])
  if row in {'TX1:165','TX1:166','TX1:167'}:assert 'ONLY deployed SolanaDigest'in f['root_domain']
  assert 'RECLASSIFICATION'in f['trust']and 'none added/removed'in f['trust']
 a=p['admission'];assert a['status']=='PASS'and not a['target_established']
 assert a['raw_ax2']['roots']==21 and a['raw_ax2']['all_equal_collectAxioms']and a['NFX']['exit']==0
 assert a['NFX']['dangling']==a['NFX']['incompatible_owners']==a['NFX']['import_mismatches']==0
 assert a['ledger_credit']=='PENDING next lead ledger gate'
 return True
validate(packet)
mutations=[]
def deny(name,edit):
 p=copy.deepcopy(packet);edit(p)
 try:validate(p)
 except AssertionError:mutations.append(dict(name=name,rejected=True));return
 raise AssertionError('Mutation admitted '+name)
deny('release target overclaim',lambda p:p.update(target_established=True))
deny('missing complete carrier',lambda p:p['functions'][0].update(complete_carrier=False))
deny('missing native control',lambda p:p['functions'][0].update(native_pairs=[]))
deny('missing member',lambda p:p['functions'].pop())
deny('unassigned occurrence',lambda p:p['functions'][0].update(rows=['TX2:155']))
deny('wrong frozen body',lambda p:p['functions'][0].update(frozen_body_sha256='0'*64))
deny('wrong original obligation',lambda p:p['functions'][0].update(baseline_obligation_statement_hash='0'*64))
deny('generic backend credit',lambda p:p['functions'][5].update(root_domain='every backend'))
deny('uncompiled root',lambda p:p['functions'][0].update(lean_roots=['Missing.root']))
deny('hidden open callee',lambda p:p['functions'][1]['canonical_callees'][0].update(baseline_status='OPEN'))
deny('ledger credit before gate',lambda p:p['admission'].update(ledger_credit='CLOSED official'))
deny('NFX mismatch ignored',lambda p:p['admission']['NFX'].update(import_mismatches=1))
# Exact per-scope input snapshots; the single large deduplicated input has a hash reference.
refs={r['snapshot']:r for r in json.loads((E/'NKD_SOURCE_REFS.json').read_text())};source_checks=0;scope_checks=0
for p in E.glob('NKD_[LK]???/receipt.json'):
 rc=json.loads(p.read_text());assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert rc['env']['CARGO_TARGET_DIR'].endswith('/codex-cx-sampler-transcript-20261108/NKD_target')
 assert int(rc['swaps'])==0 and rc['source_revision'];scope_checks+=1
 for n,h in rc['source_hashes'].items():
  q=p.parent/'sources'/n
  if not q.exists():
   ref=refs[str(q.relative_to(E))];q=E/ref['retained_input'];assert ref['sha256']==h
  assert H(q)==h,(p,n);source_checks+=1
 if rc['kind']=='lean':
  assert rc['exit_status']==0
  assert all('sorryAx'not in l for l in rc['print_axioms'])
# Accepted new modules are byte-identical to the last successful compilation.
latest={}
for p in sorted(E.glob('NKD_L???/receipt.json')):
 r=json.loads(p.read_text())
 if r['kind']=='lean'and r['exit_status']==0:
  for n,h in r['source_hashes'].items():
   if n.startswith('NKD_generated/')and n.endswith('.lean'):latest[n]=h
for n,h in latest.items():assert H(E/n)==h,n
for p in(E/'NKD_generated').glob('NKD_*.lean'):
 assert not re.search(r'^\s*(?:axiom|sorry|admit)\b',p.read_text(),re.M)
 assert 'native_decide'not in p.read_text()
# Full metadata retained once; resolve features for every crate in every new run.
index=json.loads((E/'NKD_GRAPH_INDEX.json').read_text())
for a,v in index['attempts'].items():
 data=lzma.decompress((E/v['graph_file']).read_bytes());assert hashlib.sha256(data).hexdigest()==v['graph_sha256'];m=json.loads(data)
 assert len(m['resolve']['nodes'])==v['feature_crates']and all('features'in n for n in m['resolve']['nodes'])
# No new shipped source changes, no files larger than the job limit, no build outputs.
assert not subprocess.check_output(['git','diff','--name-only','17f68777903','--','crates','programs','Cargo.lock'],text=True).strip()
assert not [p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20*1024*1024]
assert not list(E.rglob('__pycache__'))
# All compressed evidence has its original-byte digest; generate missing digests only in packaging, never here.
compressed=0
for p in E.rglob('*.xz'):
 q=Path(str(p)[:-3]+'.sha256');assert q.is_file(),str(q)
 assert hashlib.sha256(lzma.decompress(p.read_bytes())).hexdigest()==q.read_text().split()[0];compressed+=1
out=dict(status='PASS',candidate_rows=8,official_ledger_unchanged=True,source_snapshots=source_checks,capped_scopes=scope_checks,compressed_pairs=compressed,mutation_denials=mutations,new_trust_rows=[],quarantined_credits=[],suspended_credits=[],target_established=False)
(E/'NKD_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n');print('PASS: eight packets; '+str(source_checks)+' source snapshots; '+str(len(mutations))+' overclaim/missing-evidence mutations rejected')
