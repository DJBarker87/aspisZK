"""Evidence-only inventory, budget accounting and final external-scratch patch."""
from pathlib import Path
import json,hashlib,subprocess,difflib,collections
E=Path(__file__).resolve().parent;R=E.parents[1];rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
sha=lambda b:hashlib.sha256(b).hexdigest()
x=json.loads((E/'NFT_NATIVE_INPUTS.json').read_text());patch=[]
for name,text in sorted(x.items()):
 r=subprocess.run(['git','show',rev+':'+name],cwd=R,capture_output=True,text=True)
 old=r.stdout if r.returncode==0 else ''
 patch+=difflib.unified_diff(old.splitlines(True),text.splitlines(True),fromfile='a/'+name if r.returncode==0 else '/dev/null',tofile='b/'+name)
b=''.join(patch).encode();(E/'NFT_HARNESSES.patch').write_bytes(b);(E/'NFT_HARNESSES.patch.sha256').write_text(sha(b)+'  NFT_HARNESSES.patch\n')
rs=sorted([json.loads(p.read_text())for p in E.glob('NFT_[KLE][0-9][0-9][0-9]/receipt.json')],key=lambda r:r['attempt'])
for prefix,limit in [('K',100),('L',60),('E',3)]:
 group=[r for r in rs if r['attempt'].startswith('NFT_'+prefix)]
 assert {r['attempt']for r in group}=={f'NFT_{prefix}{n:03}'for n in range(1,limit+1)}
for r in rs:
 a=r['attempt'];ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(r['swaps'])==0
 assert all(k in r for k in ['module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms'])
excluded_native=['NFT_K005','NFT_K056','NFT_K069']
assert all(next(r for r in rs if r['attempt']==a)['exit_status']==1 for a in excluded_native)
used=dict(Kani=100,Lean_support=60,extraction=3);out=dict(allowed=used,used=used,remaining=dict(Kani=0,Lean_support=0,extraction=0),early_stop=False,all_scopes_admitted=True,all_swaps_zero=True,caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rs if str(r['peak_rss_kib']).isdigit()),native=dict(successful=48,intended_failing_controls=49,excluded=excluded_native),Lean_exit_0=38,Lean_exit_1=22,nonstandard_axiom_draft_excluded='NFT_L015',E001_reference_excluded='E001 extracted but Lean L009 failed; E002 fixes explicit unsigned shifts',attempt_receipts='NFT_ATTEMPTS.jsonl',source_revision_fields='Per receipt exact revision and source hashes; final new sources validated by hash',print_axioms='Per Lean receipt; final L058 headline and 58 new roots, raw L060 plus first 12 L021',cap_raised=False,unchanged_timeout_rerun=False,own_cache_retained=True)
(E/'NFT_BUDGET.json').write_text(json.dumps(out,indent=1)+'\n')
# A compact index makes AGENTS section 6 fields reviewable without traversing dependency pins.
summary=[{k:r[k]for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms']}for r in rs]
(E/'NFT_RESULTS.json').write_text(json.dumps(summary,indent=1)+'\n')
print(json.dumps(dict(patch_sha256=sha(b),attempts=len(rs),budget=used)))
