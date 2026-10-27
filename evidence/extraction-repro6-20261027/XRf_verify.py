from pathlib import Path
import hashlib,json,re,subprocess
B=Path(__file__).resolve().parent
errors=[]
def check(c,msg):
 if not c:errors.append(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[]
for p in sorted(B.glob('XRf_*/receipt.json')):
 r=json.loads(p.read_text());receipts.append(r)
 check(r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},'limits '+r['attempt'])
 check(r['swaps']=='0','swap '+r['attempt'])
 for n,h in r['source_hashes'].items():check(sha(p.parent/'sources'/n)==h,'source snapshot '+r['attempt']+' '+n)
 check(r.get('source_revision') is not None and r.get('deps_fingerprint') is not None,'provenance '+r['attempt'])
 check(bool(r.get('print_axioms')),'axioms applicability '+r['attempt'])
 check(r['reservation_retries']==0,'retries '+r['attempt'])
 a=json.loads((B/(r['attempt']+'-reservation.json')).read_text());check(a['allowed'],'admission '+r['attempt'])
 if r['kind']=='kani':
  log=(p.parent/'stdout.log').read_text();check(r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in log,'Kani '+r['attempt'])
  check('profile [optimized]' in log,'optimized '+r['attempt'])
check(len(receipts)==14,'attempt count')
check([r['exit_status'] for r in receipts[:4]]==[1,0,0,2],'extraction exits')
inv=json.loads((B/'XRf_closed_release_candidate_tx1_inventory.json').read_text())
check(inv['ready_for_aeneas'] and inv['has_errors'] is False and not inv['missing_callees'],'preflight')
check(len(inv['release_opaque'])==6,'six leaves')
check(sum(len(f['callees']) for f in inv['functions'])==1545,'call count')
check(sha(B/'XRf_Top.BEFORE.lean.txt')==sha(B/'XRf_Top.AFTER.lean.txt'),'before/after')
root=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
check(sha(root/'lean/Rc10_Top.lean')==sha(B/'XRf_Top.AFTER.lean.txt'),'actual top unchanged')
recount=json.loads((B/'XRf_recount.json').read_text());check(sha(root/recount['ledger_path'])==recount['ledger_sha256'],'ledger unchanged')
host=json.loads((B/'XRf_HostAudit.json').read_text());old=json.loads((B.parent/'extraction-repro5-20261027/XRe_HostAudit.json').read_text())
check(host['changed_source_files']==[] and host['files_checked']==7978,'release source')
check(host['runner_matches_coherent'],'coherent runner')
oldtools={x['path']:x['sha256'] for x in old['tools']}
for x in host['tools']:check(oldtools[x['path']]==x['sha256'],'tool drift '+x['path'])
check(host['generated_outputs']==[],'output count')
cleanup=json.loads((B/'XRf_Cleanup.json').read_text());check(cleanup['live_own_provers']==[],'live own prover')
for p in B.rglob('*'):
 if p.is_file():check(not(p.suffix in ['.llbc','.olean','.ir','.tgz','.gz','.so','.bin']),'binary '+str(p))
report=dict(errors=errors,attempts=len(receipts),extraction_used=4,extraction_budget=4,kani_used=10,kani_budget=10,kani_passed=10,lean_used=0,lean_budget=100,lean_blocker='No Types/Funs emitted; no new Lean theorem introduced; inherited XRe_L002 reused without re-proof',max_peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),max_cgroup_peak_bytes=max(int(r['cgroup_memory_peak_bytes']) for r in receipts),wall_seconds_sum=sum(r['wall_seconds'] for r in receipts),swaps=0,top_premises_removed=0,delta={'T':0,'P':0,'G':0,'C':0},print_axioms='N/A for all14 extraction/Kani attempts; no new top theorem')
(B/'XRf_Verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report));assert not errors,errors
