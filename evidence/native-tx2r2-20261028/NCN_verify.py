"""Static evidence validation; no prover replay."""
from pathlib import Path
import json,hashlib,re,subprocess,collections
E=Path(__file__).resolve().parent
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('NCN_[KL][0-9][0-9][0-9]/receipt.json'))]
assert len({r['attempt'] for r in receipts})==len(receipts)
assert len((E/'NCN_ATTEMPTS.jsonl').read_text().splitlines())==len(receipts)
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in receipts:
 assert r['limits']==limits,(r['attempt'],r['limits'])
 assert str(r['swaps'])=='0'
 ad=json.loads((E/(r['attempt']+'-reservation.json')).read_text());assert ad['allowed'] is True
 assert r['source_revision'] and r['source_hashes']
 assert r['wall_seconds']>=0 and int(r['peak_rss_kib'])>0
 assert not any('sorry' in line or 'axiom ' in line for line in r.get('print_axioms',[])) if r['exit_status']==0 and r['kind']=='lean' else True
kani=[r for r in receipts if r['kind']=='kani'];lean=[r for r in receipts if r['kind']=='lean']
assert len(kani)==70 and len(lean)==24
lock=hashlib.sha256(subprocess.check_output(['git','show','4bb3b3f5:Cargo.lock'])).hexdigest()
counts=collections.Counter();classes={}
for r in kani:
 a=r['attempt'];out=(E/a/'stdout.log').read_text();graph=json.loads((E/(a+'-graph-check.json')).read_text())
 assert graph['graph_matches_frozen'] and not graph['edge_errors'] and not graph['new_package_tuples']
 assert (E/(a+'-lock-after.log')).read_text().strip()==lock
 assert (E/(a+'-lock-before.log')).read_text().strip()==lock
 assert '--locked' not in r['command'] and r['env']['CARGO_NET_OFFLINE']=='true'
 assert r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 k='timeout' if 'CBMC timed out' in out else 'codegen' if 'could not compile' in out else 'unwind' if 'Failed Checks: unwinding assertion' in out else 'pass' if 'VERIFICATION:- SUCCESSFUL' in out else 'fail'
 counts[k]+=1;classes[a]=k
pairs=[(1,2),(3,4),(5,6),(10,11),(12,13),(16,17),(18,19),(22,20),(23,25),(26,27),(30,31),(32,33),(34,35),(36,37),(38,39),(40,41),(42,43),(44,45),(46,47),(50,48),(56,57),(59,60),(61,62),(63,64),(70,71),(72,73),(74,75)]
for pos,neg in pairs:
 assert classes[f'NCN_K{pos:03}']=='pass' and classes[f'NCN_K{neg:03}']=='fail'
audit=json.loads((E/'NCN_L024/receipt.json').read_text());assert audit['exit_status']==0
assert len(audit['print_axioms'])==77
allowed={'propext','Classical.choice','Quot.sound'}
for line in audit['print_axioms']:
 if 'depends on axioms:' in line:
  actual=set(re.search(r'\[(.*)\]',line).group(1).split(', '));assert actual<=allowed,line
source_checks={}
for p in sorted(Path('lean').glob('NCN_*.lean')):
 successful=[r for r in lean if r['module']==p.stem and r['exit_status']==0];assert successful,p
 r=successful[-1];digest=hashlib.sha256(p.read_bytes()).hexdigest()
 assert r['source_hashes']['NCN_generated/'+p.name]==digest
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b|maxHeartbeats|maxRecDepth',p.read_text(),re.M)
 source_checks[str(p)]=dict(sha256=digest,successful_attempt=r['attempt'])
assert not subprocess.check_output(['git','diff','--name-only','c4e0233d','--','crates','programs']).strip()
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
end=json.loads((E/'NCN_END.json').read_text());assert not end['scratch_drift'] and not end['cache_drift']
assert len(end['owned_scopes'])==94
result=dict(budget={'kani':len(kani),'kani_limit':70,'lean':len(lean),'lean_limit':70},kani_results=dict(counts),kani_by_attempt=classes,matched_pairs=pairs,excluded_caller_credits={'NCN_K050':'slice shape incomplete controls','NCN_K051':'slice real-body fidelity control only; stub control codegen failed','NCN_K077':'positive unreachable-contains check has no matching negative under the generic-stub configuration; no native credit'},lean_pass=sum(r['exit_status']==0 for r in lean),lean_rejected=sum(r['exit_status']!=0 for r in lean),audit_theorems=77,new_theorems=16,axioms=sorted(allowed),new_sources=source_checks,lock_sha256=lock,kmx_patch_sha256=hashlib.sha256(subprocess.check_output(['git','show','HEAD:evidence/kani-mitig-20261028/KMX_copy_stubs.patch'])).hexdigest(),frozen_rust='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',repo_shipped_changes=[],peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swap=0,scope_count=94)
(E/'NCN_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['budget','kani_results','lean_pass','lean_rejected','audit_theorems','new_theorems','peak_rss_kib','swap','scope_count']}))
