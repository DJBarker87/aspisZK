"""Read-only reconstruction and review of immutable native receipts."""
from pathlib import Path
import subprocess,hashlib,json
r=Path(__file__).resolve().parents[3]
e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-resume/native'
rel='crates/aspis-prover/src/state_only_entropy_prover_rw_stream_kani.rs'
s=(r/rel).read_text();old=subprocess.check_output(['git','show','49bf51d3e9:'+rel],cwd=r).decode()
assert s.startswith(old)
versions={}
def prefixes(t):
 for i in range(1,len(t.splitlines(keepends=True))+1):
  z=''.join(t.splitlines(keepends=True)[:i]);versions[hashlib.sha256(z.encode()).hexdigest()]=z
prefixes(s);prefixes(old)
failed=s[:s.index('\n#[kani::proof]',s.index('fn drop_array_cut'))]
failed=failed.replace('fn drop_array_cut<Z: zeroize::Zeroize,const N:usize>(_bytes: &mut [Z;N]) {}','fn drop32_cut(_bytes: &mut [u8;32]) {}\nfn drop64_cut(_bytes: &mut [u8;64]) {}')
failed+='''
#[kani::proof]
#[kani::unwind(65)]
#[kani::stub(super::entropy_nonzero32,nonzero)]
#[kani::stub(getrandom::fill,control_stream)]
#[kani::stub(<[u8;32] as zeroize::Zeroize>::zeroize,drop32_cut)]
#[kani::stub(<[u8;64] as zeroize::Zeroize>::zeroize,drop64_cut)]
fn control5_drop_cut() {control::<5,false>();}
'''
prefixes(failed)
(e/'sources').mkdir(exist_ok=True)
rows=[]
for p in sorted(e.glob('entropy-*/receipt.json')):
 x=json.loads(p.read_text());sha=x['source_sha256'][rel]
 assert sha in versions,(p,sha)
 dst=e/'sources'/(sha+'.rs.txt');dst.write_text(versions[sha]);assert hashlib.sha256(dst.read_bytes()).hexdigest()==sha
 rows.append(dict(attempt=x['attempt'],target=x['target'],exit_status=x['exit_status'],wall_seconds=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],cgroup_memory_peak_bytes=x['cgroup_memory_peak_bytes'],cgroup_memory_events=x['cgroup_memory_events'],limits=x['limits'],source_sha256=sha,source_snapshot=str(dst.relative_to(e)),actual_base_revision='49bf51d3e9afab9691df3d2aacbba4905dda4a05',raw_revision_label=x['source_revision'],print_axioms='N/A: Kani'))
assert len(rows)==11
result=dict(invocations=len(rows),passed=sum(x['exit_status']==0 for x in rows),timeouts=sum(x['exit_status']==124 for x in rows),compile_rejections=sum(x['exit_status']==1 for x in rows),root_premises_removed=0,production_prefix_unchanged=True,previous_source_sha256=hashlib.sha256(old.encode()).hexdigest(),scope='Native support/control/payload with explicit generic array destructor cut; not E1, actual Drop composition, or native extraction adequacy',attempts=rows)
(e/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
print({k:v for k,v in result.items() if k!='attempts'})
