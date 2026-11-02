"""Fail-closed focused receipt and source-ledger reconciliation for D550."""
from pathlib import Path
import json,re,hashlib,subprocess,lzma
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inv=json.loads((R/'D550-final-host-inventory.json').read_text())
for n,h in inv['hashes'].items():
 p=R/n.removeprefix('resume18/');raw=p.read_bytes()if p.exists()else lzma.decompress(p.with_name(p.name+'.xz').read_bytes())
 assert hashlib.sha256(raw).hexdigest()==h,n
assert '0 loaded units listed'in inv['scopes']
receipts={};new=[];failed=[]
for p in sorted(R.glob('lean-790*/receipt/receipt.json')):
 r=json.loads(p.read_text());receipts[r['module']]=r
 if not 79028<=r['attempt']<=79096:continue
 assert r['source_sha256']==sha(p.parent.parent/'source.lean')
 assert r['source_sha256']==hashlib.sha256(subprocess.check_output(['git','cat-file','blob',r['project_source_authority']['blob']])).hexdigest()
 assert r['swaps']==0 and r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 sub=json.loads((p.parent.parent/'submission.json').read_text())
 assert sub['shared_sources_written']is False
 admission=json.loads((p.parent.parent/'reservation.json').read_text());assert admission['allowed']is True
 if r['exit_status']==0:
  log=(p.parent/'stdout.log').read_text();assert 'sorryAx'not in log and 'error:'not in log
  axioms=re.findall(r'depends on axioms: \[([^\]]*)\]',log)
  assert axioms or 'does not depend on any axioms'in log
  assert all(set(a.replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}for a in axioms)
 else:failed.append(dict(attempt=r['attempt'],module=r['module'],exit=r['exit_status'],source_sha256=r['source_sha256'],credit=False))
 new.append({k:r[k]for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','lean_source_revision','source_sha256','print_axioms']})
def passed(m):
 assert m in receipts and receipts[m]['exit_status']==0,m
 assert receipts[m]['source_sha256']==sha(D/'lean'/(m+'.lean')),m+' current source not compiled'
for name in ['PV_B3P_PreparedSource550227','PV_B3P_InternalMaps550227','PV_B3P_InternalPairSource550227','PV_B3P_FromFnFour550227','PV_B3P_RawRows550227','PV_B3P_RawDebug550227','PV_B3P_RawDebugLoops550227','PV_B3P_RawPack0550227','PV_B3P_RawPack1550227','PV_B3P_RawPack2550227','PV_B3P_RawPack3550227','PV_B3P_FourIndex550227','PV_B3P_RawRowContinuation550227','PV_B3P_RawSuffix550227']:
 passed(name)
updates={
 'qm31_sum_products3_prepared':('PV_B3P_PreparedSource550227','PV_B3P_Association550227.prepared_source_link550','PREPARED-SOURCE-D550.json'),
 'interpolated_internal_pair':('PV_B3P_InternalPairSource550227','PV_B3P_Association550227.internal_pair_source_link550','INTERNAL-PAIR-SOURCE-D550.json')}
raw_pass=receipts.get('PV_B3P_RawSource550227',{}).get('exit_status')==0
if raw_pass:
 passed('PV_B3P_RawSource550227')
 for i in range(5):passed(f'PV_B3P_RawTail{i}550227')
 passed('PV_B3P_RawTails550227')
 passed('PV_B3P_RawReferenceFactor550227')
 for i in range(1,5):passed(f'PV_B3P_RawRefTail{i}550227')
 updates['external_local_packed_raw']=('PV_B3P_RawSource550227','PV_B3P_Association550227.raw_source_link550','RAW-SOURCE-D550.json')
# Existing exact reference replays are reused, never rerun for budget use.
for file,names in [('REFERENCE-PROJECTED-D547.json',['reference_field.qm31_sum_products3_prepared','reference_poseidon.interpolated_internal_pair']),('POSEIDON-REFERENCE-D543.json',[])]:
 x=json.loads((R/file).read_text());assert not x.get('holes',[])
 if names:assert all(n in [d['declaration']for d in x['declarations']]for n in names)
old=json.loads((R/'PER-FUNCTION-D547.json').read_text())
for row in old['functions']:
 if row['function']in updates:
  module,theorem,dossier=updates[row['function']]
  row.update(local_body_association='BOUND',route='Lean equality + own-1 structural',theorem=theorem,evidence=dossier,remaining='Named callee source rows and whole std/D188/matrix/callback, optimized dispatch where distinct, and V370/D381/D386 remain; no endpoint closure')
  x=json.loads((R/dossier).read_text());x['status']='BOUND locally by script-checked whole source argument and accepted complete-Result Lean equality; no whole source-cone claim';x['accepted_attempt']=receipts[module]['attempt'];(R/dossier).write_text(json.dumps(x,indent=2)+'\n')
bound=24+len(updates);assert sum(r['local_body_association']=='BOUND'for r in old['functions'])==bound
old['counts']=dict(total=36,bound=bound,open=36-bound,direct_extraction=4,Kani=2,Lean_equality_with_structural_source_binding=18+len(updates))
old['new_associations']=list(updates);old['pending_uncredited']=[]if raw_pass else['external_local_packed_raw: staged raw bridge pending; all failed raw Kani gates stay no credit']
(R/'PER-FUNCTION-D550.json').write_text(json.dumps(old,indent=2)+'\n')
t=json.loads((R/'TALLY-resume18.json').read_text())
assert inv['extraction_receipts']==8 and inv['kani_receipts']==5
assert not list(R.glob('K79107*/receipt/receipt.json'))
out=dict(target=old['target'],entry_revision='688ffae818',coverage=old['counts'],new_lean=new,failed_no_credit=failed,host_artifacts_verified=len(inv['hashes']),budget=dict(remaining=dict(lean=80-t['lean_attempts'],extraction=22,kani=25),next_lean=t['next_unused_id'],audits_remaining=[79099],next_extraction='N79168, fresh scan required',next_Kani='K79108/09, fresh scan required; K79107 retired'),raw_route='total structural/Lean, no Kani credit',axioms='Only propext/Classical.choice/Quot.sound in accepted new declarations; rejected and stopped attempts earn no credit',premise_changes=dict(removed=[],added=[],weakened=[]),scope='Local source-body associations; original79/41 inventory remains separate. Exact OracleBridge38.selected_callback op227 remains OPEN.',full_endpoint_replay='not run; no unchanged full regression',checkpoint='Context checkpoint, not budget exhaustion')
(R/'verification-summary-D550.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(coverage=old['counts'],budget=out['budget'],accepted_new=sum(r['exit_status']==0 for r in new),failed_new=len(failed),host_hashes=len(inv['hashes']))))
