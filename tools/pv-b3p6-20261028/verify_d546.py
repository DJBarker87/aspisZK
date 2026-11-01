"""Reconcile accepted new local proofs separately from staged source maps."""
from pathlib import Path
import json,re,hashlib,subprocess,lzma
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inv=json.loads((R/'D546-final-host-inventory.json').read_text())
for n,h in inv['hashes'].items():
 p=R/n.removeprefix('resume18/'); b=p.read_bytes()if p.exists()else lzma.decompress(p.with_name(p.name+'.xz').read_bytes());assert hashlib.sha256(b).hexdigest()==h,n
assert '0 loaded units listed'in inv['scopes']
new=[]
for p in sorted(R.glob('lean-790*/receipt/receipt.json')):
 r=json.loads(p.read_text())
 if r['attempt']<79009 or r['attempt']==79097:continue
 assert r['source_sha256']==sha(p.parent.parent/'source.lean')
 assert r['swaps']==0 and r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['source_sha256']==hashlib.sha256(subprocess.check_output(['git','cat-file','blob',r['project_source_authority']['blob']])).hexdigest()
 if r['exit_status']==0:
  log=(p.parent/'stdout.log').read_text();assert 'sorryAx'not in log and 'error:'not in log
  ax=re.findall(r'depends on axioms: \[([^\]]*)\]',log)
  assert ax or 'does not depend on any axioms'in log
  assert all(set(a.replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}for a in ax)
 new.append({k:r[k]for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','lean_source_revision','source_sha256','print_axioms']})
rounds=next(r for r in new if r['module']=='PV_B3P_RoundSource546227');assert rounds['exit_status']==0
ref=json.loads((R/'ROUND-REFERENCE-D546.json').read_text());assert len(ref['declarations'])==39 and ref['holes']==[]
r=json.loads((R/'N79162/receipt/receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0
old=json.loads((R/'PER-FUNCTION-D543.json').read_text());updates={
 'full_round':'round_qplain_source_link546',
 'full_round_m31_constants':'round_mplain_source_link546',
 'full_round_packed':'round_qpacked_source_link546',
 'full_round_m31_constants_packed':'round_mpacked_source_link546'}
for row in old['functions']:
 if row['function']in updates:row.update(local_body_association='BOUND',route='Lean equality + own-1 structural',theorem=updates[row['function']],evidence='ROUND-SOURCE-D546.json / ROUND-REFERENCE-D546.json / Lean79009',remaining='Whole std/D188/matrix/callback and V370 retained; no endpoint closure')
assert sum(r['local_body_association']=='BOUND'for r in old['functions'])==16
old['counts']=dict(total=36,bound=16,open=20,direct_extraction=4,Kani=2,Lean_equality_with_structural_source_binding=10)
old['new_associations']=list(updates);old['pending_uncredited']=['leading_pair_packed','active_literal','pattern_values_literal','add_schedule_lanes','path_lanes_literal','raw repaired gate']
(R/'PER-FUNCTION-D546.json').write_text(json.dumps(old,indent=2)+'\n')
t=json.loads((R/'TALLY-resume18.json').read_text())
out=dict(target=old['target'],entry_revision='8d74c78aaf',coverage=old['counts'],new_lean=new,new_extraction={k:r[k]for k in ['exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms']},host_artifacts_verified=len(inv['hashes']),budget=dict(remaining=dict(lean=80-t['lean_attempts'],extraction=30-inv['extraction_receipts'],kani=30-inv['kani_receipts']),next_lean=t['next_unused_id'],audits_remaining=[79098,79099],next_extraction='N79163',next_Kani='K79104: unlaunched, refused admissions; matched positive K79105'),axioms='New RoundSource546227 printed five declarations; only propext, Classical.choice, Quot.sound. New combined audit is staged, NOT compiled.',premise_changes=dict(removed=[],added=[],weakened=[]),refusals=t.get('refusals',[]),full_endpoint_replay='NOT run; whole source-cone and actual selected_callback remain open',evidence_class='own-1 structural source argument plus Lean complete-Result equality; no machine proof or new Kani credit')
(R/'verification-summary-D546.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(coverage=old['counts'],budget=out['budget'],host_hashes=len(inv['hashes']))))
