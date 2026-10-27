"""Verify retained native receipts and reconstruct exact changed source snapshots."""
from pathlib import Path
import json,hashlib,re,subprocess
r=Path(__file__).resolve().parents[2];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026';n=e/'native';snap=e/'native-source';snap.mkdir(exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest();current=(r/'crates/aspis-r1-cost-probe/src/r1_wire.rs').read_bytes();versions={sha(current):current}
for marker in [b'\n#[cfg(kani)]\nmod pdict_typenum_contracts',b'\n#[cfg(kani)]\nmod pdict_numeric_contracts',b'\n#[cfg(kani)]\nmod pdict_comparison_contracts',b'\n#[cfg(kani)]\nmod pdict_primitive_contracts',b'\n#[cfg(kani)]\nmod pdict_ordering_contracts',b'\n#[cfg(kani)]\nmod pdict_representation_contracts',b'\n#[cfg(kani)]\nmod pdict_error_value_contracts',b'\n#[cfg(kani)]\nmod pdict_options_contracts']:
 b=current[:current.index(marker)];versions[sha(b)]=b
proof=(r/'crates/aspis-r1-cost-probe/src/prover.rs').read_bytes();versions[sha(proof)]=proof
for h,b in versions.items():(snap/(h+'.rs.txt')).write_bytes(b)
rows=[];other=[]
for p in sorted(n.glob('*/receipt.json')):
 x=json.loads(p.read_text());assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 row={k:x[k] for k in ['attempt','target','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes','cgroup_swap_peak_bytes','deps_fingerprint','source_revision']}
 if 'cargo' in x['target'] and 'kani' in x['target']:
  for name in ['crates/aspis-r1-cost-probe/src/r1_wire.rs','crates/aspis-r1-cost-probe/src/prover.rs']:
   h=x['source_sha256'][name];assert h in versions,(p,name,h)
  assert x['environment']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  rows.append(row)
 else:other.append(row)
 assert all(int(x['cgroup_memory_events'][k])==0 for k in ['oom','oom_kill','oom_group_kill'])
assert len(rows)==20,len(rows)
assert sum(z['exit_status']==0 for z in rows)==19
out=dict(kani_runs=20,passed=19,compile_failures=1,timeouts=0,ooms=0,kani_budget_remaining=0,runs=rows,other_capped_jobs=other,scope='Source/value/schema contracts only. Complete scalar getrandom error and IEEE64 bit codecs; complete Unix OpenOptions primitive state/setter/loan frame. Typenum source-reachable instances and short path<=4/short slice<=4 tests retain those exact scopes; no universal Drop, full native effects, E1/E2, caller/RunJoin or security closure.',source_revision_note='Runner revision labels are base-plus-WIP labels; immutable exact Rust snapshots plus receipt source hashes identify what compiled. No historical proof is attributed to changed native source.',proof_harness_note='Type-only cfg(kani) standalone wrapper inputs are separately retained; existing native runner did not enumerate that new tools directory.')
(e/'native-summary.json').write_text(json.dumps(out,indent=2)+'\n');print(dict(kani=20,passed=19,other_capped_jobs=len(other)))
