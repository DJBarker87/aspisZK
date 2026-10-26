"""Index retained native receipts and qualify their standalone source pins.
No workload is launched, and no build infrastructure is modified.
"""
from pathlib import Path
import hashlib,json,subprocess
r=Path(__file__).resolve().parents[2];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/resumed144'
sha=lambda b:hashlib.sha256(b).hexdigest()
old=subprocess.check_output(['git','show','37ec9c9b30:tools/prover-dict-20261026/proof-std-native/lib.rs'],cwd=r)
assert (r/'tools/prover-dict-20261026/proof-std-native/lib.rs').read_bytes().startswith(old)
(e/'kani087-lib.rs.txt').write_bytes(old)
(e/'kani085-recovered-prefix.rs.txt').write_bytes(old.split(b'\n#[cfg(kani)]\nmod io_os_kind_scalar')[0])
sources={i:f'kani{i:03d}-lib.rs.txt' for i in range(79,85)}
sources.update({85:'kani085-recovered-prefix.rs.txt',86:'kani085-recovered-prefix.rs.txt',87:'kani087-lib.rs.txt',94:'kani094-097-lib.rs.txt',97:'kani094-097-lib.rs.txt',98:'kani098-lib.rs.txt',99:'kani099-lib.rs.txt',100:'kani100-lib.rs.txt',101:'kani101-lib.rs.txt'})
rows=[]
for f in sorted(e.glob('**/receipt.json')):
 x=json.loads(f.read_text());cmd=x.get('target',[])
 if 'kani' not in cmd:continue
 n=int(x['attempt'].rsplit('-',1)[1]);source=e/sources[n]
 supp=dict(actual_worktree_source_stage='bb11162de7 plus retained WIP snapshots' if n>=94 else '37ec9c9b30 and its preceding source stages',runner_source_revision_label=x['source_revision'],standalone_source=dict(path=str(source.relative_to(e)),sha256=sha(source.read_bytes())),standalone_inputs={str(p.relative_to(r)):sha(p.read_bytes()) for p in (r/'tools/prover-dict-20261026/proof-std-native').glob('Cargo.*')},qualification='Inherited runner does not enumerate this standalone proof crate. These retained source snapshots and exact standalone Cargo/lock supplement its pinned production/dependency inputs. Native runtime uses Kani0.67 embedded Rust1.93nightly53732d5e0; ambient rustc label is not that compiler. No deployed artifact association follows.')
 if n in [85,86]:supp['snapshot_qualification']='Recovered from the immutable WIP source prefix; not independently hashed by the runner at launch. 086 had no matching harness and establishes nothing.'
 (f.parent/'standalone-input-supplement.json').write_text(json.dumps(supp,indent=2)+'\n')
 rows.append({k:x[k] for k in ['attempt','target','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes','cgroup_swap_peak_bytes','limits','expected_work']})
assert len(rows)==15,len(rows)
(e/'native-summary-current.json').write_text(json.dumps(dict(runs=rows,kani_runs=15,passed=sum(z['exit_status']==0 for z in rows),timeouts=sum(z['exit_status']==124 for z in rows),other_failures=sum(z['exit_status'] not in [0,124] for z in rows),remaining=0,root_premises_removed=0,qualification='All accepted contracts retain their stated scalar/value/observer scopes. No general dynamic IO Error/Formatter carrier, native-world RunJoin or probability law is supplied.'),indent=2)+'\n')
print('Kani',len(rows),'passed',sum(z['exit_status']==0 for z in rows))
