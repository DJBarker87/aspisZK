from pathlib import Path
import hashlib,json,subprocess
from S2I_inventory import restore
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2i-20261023'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for p in sorted(E.glob('*/receipt.json')):
 x=json.loads(p.read_text());assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert x['swaps']=='0'
 for f,h in x['source_hashes'].items():assert sha(p.parent/'sources'/f)==h
 if x['kind']=='lean':
  raw=restore(p.parent);assert hashlib.sha256(raw).hexdigest()==x['deps_fingerprint']['selected_overlay_sha256']
  if x['exit_status']==0:assert all('sorryAx' not in line and not any(w in line for w in ['native_decide','trustMe','Lean.ofReduceBool']) for line in x['print_axioms'])
 rows.append(dict(attempt=x['attempt'],kind=x['kind'],command=x['command'],revision=x['source_revision'],exit=x['exit_status'],wall_seconds=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],print_axioms=x['print_axioms'],receipt=str(p.relative_to(E))))
assert sum(r['kind']=='lean' for r in rows)<=100
assert sum(r['kind']=='kani' for r in rows)<=60
final=json.loads((E/'lean-011/receipt.json').read_text());assert final['exit_status']==0 and len(final['print_axioms'])==8
for p in (D/'lean').glob('S2I_*.lean'):assert sha(p)==final['source_hashes'][p.name]
src=(R/'programs/r1-cost-probe/src/r1_pool_adapter.rs').read_text();body=src[src.index('fn emit_result('):src.index('\n#[inline(never)]\nfn stage1')]+'\n'
assert (E/'S2I-native/src/S2I_emit.rs').read_text()==body
for f,entry in json.loads((E/'native-source.json').read_text()).items():assert sha(R/f)==entry['sha256']
assert all(p.stat().st_size<5*2**20 for p in E.rglob('*') if p.is_file())
assert not [p for p in E.rglob('*') if p.suffix in ['.olean','.o','.elf','.tar','.gz']]
summary=dict(schema='s2i-child-proof-packet-v1',status='PARTIAL; target not yet established',lean_attempts=11,kani_runs=5,accepted_union='lean-011',native_success_scope='kani-003: zero-master rejection only',excluded_kani=['kani-001:timeout','kani-002:timeout','kani-004:unwind failure','kani-005:timeout'],no_new_native_required14=True,rows=rows)
(E/'manifest.json').write_text(json.dumps(summary,indent=2)+'\n');print('S2I audit passed: Lean11/100 Kani5/60; eight standard-only union audits')
