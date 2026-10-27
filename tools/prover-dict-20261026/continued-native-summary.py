"""Read-only native receipt/input qualification; never launches workloads."""
from pathlib import Path
import json,hashlib,subprocess
r=Path(__file__).resolve().parents[2];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/continued';sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[]
for f in sorted(e.glob('pdict-*/receipt.json')):
 x=json.loads(f.read_text());n=int(x['attempt'].rsplit('-',1)[1]);supp=dict(worktree_base_revision='aa357f7644' if n<=68 else '9bfc555ad3',raw_source_revision_label=x['source_revision'],qualification='Inherited runner pins an old snapshot label; actual base plus exact retained WIP source/Cargo/lock/LLBC inputs qualify these focused checks. No deployed artifact identity or native full caller closure is asserted.')
 if n in [73,77,78]:
  src=e/({73:'kani073-lib.rs.txt',77:'kani077-lib.rs.txt',78:'kani078-state-only-hiding.rs.txt'}[n]);supp['exact_extra_source']={'path':str(src.relative_to(e)),'sha256':sha(src.read_bytes())}
  if n==78:
   assert x['source_sha256']['crates/aspis-prover/src/state_only_hiding.rs']==sha(src.read_bytes())
  supp['kani_embedded_toolchain']='Pinned separately by existing resume/resume-provenance.json, not the ambient rustc field. Kani0.67 uses rustc1.93nightly53732d5e0.'
 (f.parent/'continued-input-supplement.json').write_text(json.dumps(supp,indent=2)+'\n')
 rows.append(dict(attempt=x['attempt'],command=x['target'],exit=x['exit_status'],wall_seconds=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],cgroup_memory_peak_bytes=x['cgroup_memory_peak_bytes'],cgroup_swap_peak_bytes=x['cgroup_swap_peak_bytes'],limits=x['limits'],expected_work=x['expected_work']))
k=[z for z in rows if 'kani' in z['command']]
assert len(k)==3
(e/'native-summary.json').write_text(json.dumps(dict(runs=rows,kani_runs=3,kani_passed=sum(z['exit']==0 for z in k),kani_timeouts=sum(z['exit']==124 for z in k),kani_remaining=0,qualification='Formatter077 timeout proves nothing;073 borrow adapter and078 volatile mask-cell frame only. No general Formatter/File/IO Error, effect-order, Drop or RunJoin association.'),indent=2)+'\n')
p=r/'crates/aspis-prover/src/state_only_hiding.rs';old=subprocess.check_output(['git','show','9bfc555ad3:crates/aspis-prover/src/state_only_hiding.rs'],cwd=r);now=p.read_bytes();assert now.startswith(old);tail=now[len(old):];assert tail.lstrip().startswith(b'#[cfg(kani)]')
(e/'production-prefix.json').write_text(json.dumps(dict(path=str(p.relative_to(r)),base_revision='9bfc555ad3',prefix_sha256=sha(old),prefix_bytes=len(old),current_sha256=sha(now),appended_bytes=len(tail),qualification='Only an appended cfg(kani) harness; production prefix unchanged. Existing ELF mismatches and historical timing scope are retained, not silently repinned.'),indent=2)+'\n')
print('native runs',len(rows),'Kani',len(k))
