from pathlib import Path
import hashlib,json,re,subprocess
from S2J_inventory import restore
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2j-20261023'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts={p.parent.name:json.loads(p.read_text()) for p in sorted(E.glob('*/receipt.json'))}
assert len(receipts)==3
for name,x in receipts.items():
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert x['swaps']=='0'
 for f,h in x['source_hashes'].items():assert sha(E/name/'sources'/f)==h,(name,f)
 reserve=json.loads((E/(name+'-reservation.json')).read_text());assert reserve['allowed'] and reserve['bounded_reserved_bytes']+reserve['requested_bytes']<=reserve['safe_limit_bytes']
 if x['kind']=='lean':
  assert x['exit_status']==0
  assert hashlib.sha256(restore(E/name)).hexdigest()==x['deps_fingerprint']['selected_overlay_sha256']
  assert all('sorryAx' not in l and all(a.strip() in ['propext','Classical.choice','Quot.sound'] for a in re.search(r'\[(.*)\]',l).group(1).split(',')) for l in x['print_axioms'])
 else:
  log=(E/name/'stdout.log').read_text()
  assert x['exit_status']==1 and '1 of 233 failed (4 unreachable)' in log and 'assertion failed: native_cut1(&[], 3) == owned_cut1(&[3,10], 3)' in log
assert len([x for x in receipts.values() if x['kind']=='lean'])==2
assert len([x for x in receipts.values() if x['kind']=='kani'])==1
assert sha(D/'lean/S2J_Cut1Obstruction.lean')==receipts['lean-002']['source_hashes']['S2J_Cut1Obstruction.lean']
# Confirm projected native and owned snippets mechanically, ignoring whitespace.
strip=lambda s:re.sub(r'\s+','',s)
src=(R/'programs/r1-cost-probe/src/r1_pool_adapter.rs').read_text()
guard=src[src.index('    if !(data == &[3, 10]'):src.index('    let proof_account',src.index('fn stage1('))]
probe=(E/'S2J-cut1/src/lib.rs').read_text()
native=probe[probe.index('    if !(data'):probe.index('// S2E owned')]
assert strip(guard.replace('accounts.len()','accounts_len')) in strip(native)
owned=(D/'evidence/s2e-20261023/S2E-reference/src/S2E_Reference.rs').read_text()
body=owned[owned.index('pub fn shape1('):owned.index('pub fn admission(')].replace('pub fn shape1','fn owned_cut1')
assert strip(body) in strip(probe)
# No frozen/shipped source or another worker's source changed.
base=json.loads((E/'S2J-stage0.json').read_text())['source_revision']
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
assert all('/s2j-20261023/' in p or p.endswith('/S2J_Cut1Obstruction.lean') or p.endswith('/S2J-20261023.md') for p in changed),changed
for p in E.rglob('*'):
 if p.is_file():assert p.suffix not in ['.olean','.so','.a','.tar','.gz'],p
manifest=dict(schema='focused-extractor-proof-packet-v1',status='STOP at cut1: inherited relation lacks native invocation binding',budget={'lean':2,'kani':1},results={n:{k:x[k] for k in ['kind','command','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']} for n,x in receipts.items()},native_cuts_closed=0,required14_discharged=0)
(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('PASS: source extraction, receipts, limits, budgets, selected objects, standard axiom audits, diagnostic scope, unchanged shipped files')
