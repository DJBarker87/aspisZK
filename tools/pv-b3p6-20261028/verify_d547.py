"""Reconcile accepted evidence; every route fails closed without its receipts."""
from pathlib import Path
import json,re,hashlib,subprocess,lzma
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inv=json.loads((R/'D547-final-host-inventory.json').read_text())
for n,h in inv['hashes'].items():
 p=R/n.removeprefix('resume18/');b=p.read_bytes()if p.exists()else lzma.decompress(p.with_name(p.name+'.xz').read_bytes());assert hashlib.sha256(b).hexdigest()==h,n
assert '0 loaded units listed'in inv['scopes']
receipts={};new=[]
for p in sorted(R.glob('lean-790*/receipt/receipt.json')):
 r=json.loads(p.read_text());receipts[r['module']]=r
 if r['attempt']<79012 or r['attempt']==79097:continue
 assert r['source_sha256']==sha(p.parent.parent/'source.lean')
 assert r['source_sha256']==hashlib.sha256(subprocess.check_output(['git','cat-file','blob',r['project_source_authority']['blob']])).hexdigest()
 assert r['swaps']==0 and r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 if r['exit_status']==0:
  log=(p.parent/'stdout.log').read_text();assert 'sorryAx'not in log and 'error:'not in log
  ax=re.findall(r'depends on axioms: \[([^\]]*)\]',log);assert ax or 'does not depend on any axioms'in log
  assert all(set(a.replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}for a in ax)
 new.append({k:r[k]for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','lean_source_revision','source_sha256','print_axioms']})
def passed(m):assert m in receipts and receipts[m]['exit_status']==0,m
for group,ident in [('leading',79163),('copy',79164),('schedule',79165),('packed',79166),('projected',79167)]:
 x=json.loads((R/('REFERENCE-'+group.upper()+'-D547.json')).read_text());assert not x['holes'] and x['declarations']
 r=json.loads((R/f'N{ident}/receipt/receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0
updates={
 'evaluate_state_only_poseidon_oracle_projected':('PV_B3P_ProjectedSource547227','projected_source_link547','PROJECTED-SOURCE-D547.json / REFERENCE-PROJECTED-D547.json'),
 'leading_pair_packed':('PV_B3P_LeadingSource546227','leading_source_link546','CALLER-SOURCE-D546.json / REFERENCE-LEADING-D547.json'),
 'active_literal':('PV_B3P_CopySource546227','active_literal_source_link546','COPY-SOURCE-D546.json / REFERENCE-COPY-D547.json'),
 'pattern_values_literal':('PV_B3P_CopySource546227','pattern_literal_source_link546','COPY-SOURCE-D546.json / REFERENCE-COPY-D547.json'),
 'add_schedule_lanes':('PV_B3P_ScheduleSource546227','schedule_source_link546','CALLER-SOURCE-D546.json / REFERENCE-SCHEDULE-D547.json'),
 'public_digest_lanes':('PV_B3P_DigestSource547227','public_digest_source_link547','DIGEST-SOURCE-D547.json / REFERENCE-SCHEDULE-D547.json'),
 'path_lanes_literal':('PV_B3P_PathSource547227','path_literal_source_link547','PATH-SOURCE-D546.json / REFERENCE-SCHEDULE-D547.json'),
 'external_linear_packed':('PV_B3P_PackedExternal547227','external_packed_source_link547','PACKED-EXTERNAL-SOURCE-D547.json / REFERENCE-PACKED-D547.json')}
old=json.loads((R/'PER-FUNCTION-D546.json').read_text())
for row in old['functions']:
 if row['function']in updates:
  m,t,e=updates[row['function']];passed(m)
  row.update(local_body_association='BOUND',route='Lean equality + own-1 structural',theorem=t,evidence=e,remaining='Named callee source rows and full std/D188/matrix/callback, optimized dispatch where distinct, and V370 remain open; no endpoint closure')
for i in range(8):passed(f'PV_B3P_PathCell15_{i}227')
passed('PV_B3P_NativePath15227');passed('PV_B3P_SourceAudit547227')
# Failed raw attempts remain recorded, never promoted to local source credit.
raw=[]
for ident in [79104,79105,79106]:
 paths=list(R.glob(f'K{ident}*/receipt/receipt.json'));assert len(paths)==1,(ident,paths)
 p=paths[0];r=json.loads(p.read_text());assert r['exit_status']!=0 and r['swaps']==0
 raw.append(dict(run=p.parent.parent.name,exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps']))
assert not list(R.glob('K79107*/receipt/receipt.json')), 'positive must remain unlaunched after rejected control configuration'
assert 'Kani requires overflow checks' in (R/'K79106/receipt/stdout.log').read_text()
assert sum(r['local_body_association']=='BOUND'for r in old['functions'])==24
old['counts']=dict(total=36,bound=24,open=12,direct_extraction=4,Kani=2,Lean_equality_with_structural_source_binding=18)
old['new_associations']=list(updates);old['pending_uncredited']=['external_local_packed_raw: raw Kani failed; total structural/from_fn route remains open']
(R/'PER-FUNCTION-D547.json').write_text(json.dumps(old,indent=2)+'\n')
t=json.loads((R/'TALLY-resume18.json').read_text())
out=dict(target=old['target'],entry_revision='b34b41b85b',coverage=old['counts'],new_lean=new,host_artifacts_verified=len(inv['hashes']),budget=dict(remaining=dict(lean=80-t['lean_attempts'],extraction=30-inv['extraction_receipts'],kani=30-inv['kani_receipts']),next_lean=t['next_unused_id'],audits_remaining=[79099],next_extraction='N79168',next_Kani='K79108 (K79107 unlaunched paired preparation retired)'),failed_no_credit=raw,raw_obstruction='K79104-r2 intended assertion plus three forced-MIR subtraction checks; K79105 only forced-MIR subtraction checks. K79106 compiler rejects explicit overflow-checks=off before verification; K79107 correctly unlaunched, retired. No new Kani credit.',axioms='Only propext/Classical.choice/Quot.sound in all accepted new declarations and twelve-link audit',premise_changes=dict(removed=[],added=[],weakened=[]),scope='Local source-body associations; original 79/41 historical inventory is separate. V244 and selected_callback op227 remain OPEN; no actual callback source-cone closure asserted.',full_endpoint_replay='not run; unchanged full regressions not repeated')
(R/'verification-summary-D547.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(coverage=old['counts'],budget=out['budget'],host_hashes=len(inv['hashes']))))
