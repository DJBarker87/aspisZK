"""Read-only verification and summary of retained native receipts."""
from pathlib import Path
import json,hashlib,subprocess
r=Path(__file__).resolve().parents[3]
e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/native-install'
n=e/'native'
for x in json.loads((n/'manifest.json').read_text()):
 p=n/x['path'];assert p.stat().st_size==x['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==x['sha256']
rows=[]
for p in sorted((n/'receipts').glob('entropy-native-*/receipt.json')):
 x=json.loads(p.read_text())
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert all(int(x['cgroup_memory_events'][k])==0 for k in ['oom','oom_kill','oom_group_kill'])
 rows.append({k:x[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes','cgroup_swap_peak_bytes','deps_fingerprint']})
assert len(rows)==20
counts={str(s):sum(x['exit_status']==s for x in rows) for s in sorted(set(x['exit_status'] for x in rows))}
assert counts['0']==12 and counts['124']==7
p=r/'crates/aspis-prover/src/state_only_entropy.rs';base=subprocess.check_output(['git','show','e8d5489de3:crates/aspis-prover/src/state_only_entropy.rs']);src=p.read_bytes()
assert src.startswith(base) and src[len(base):].lstrip().split(b'#[cfg(kani)]',1)[0].strip().startswith(b'// Local native contracts')
x=json.loads((e/'kani-source-change.json').read_text());x['after_sha256']=hashlib.sha256(src).hexdigest();x['appended_bytes']=len(src)-len(base)
(e/'kani-source-change.json').write_text(json.dumps(x,indent=2)+'\n')
(e/'native-entropy-final-input.rs.txt').write_bytes(src)
summary=dict(runs=rows,actual_kani_runs=20,passed=12,compile_failures=1,timeouts=7,oom_kills=0,remaining_kani_budget=0,source_change=x,scope='Native local contracts only: Drop32/Drop64 selected byte, ABI64, borrow64, arbitrary raw error roundtrip, owner Drop/public nonce, exact OR32 predicate, zero nonce, first success/error and success/error after one rejected reply. Provider is an arbitrary tape stub, not an OS probability law.',open='Sixteen-reply native caller coverage, effects/extractor/history-conditioned E1 association, full dictionary and real RunJoin. Conditional model entropy rates are not native statements.',source_labels='Raw runner source_revision labels are inherited and stale. Exact recorded source hashes plus immutable snapshots are authoritative. Four unrelated host production files were stale before explicit source sync; earlier local entropy contracts cover only their reachable pinned entropy/zeroize code, not whole branch artifacts.',measurement='GNU time RSS may undercount timeout descendants; separate cgroup peaks are retained. All jobs used opt-level3, j4, no swap and unchanged native 6G/8G caps.',elf='Stale-input proverw116 all-three matches rejected. Current-source proverw118 default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,1563728 bytes differs from pinned d7d42f770883401e0104fb6e044f61a132fea7359943db225d581c5740fcffd0,1511216 bytes. Later features and +10% adoption timing gate not run; pins unchanged. Retained three-ELF rehash is not a fresh current-source build.')
(e/'native-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(counts)
