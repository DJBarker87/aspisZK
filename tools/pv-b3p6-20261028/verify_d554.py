"""Reconcile focused D554 receipts, source associations, feature selection and budgets."""
from pathlib import Path
import json,re,hashlib,subprocess,lzma
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inv=json.loads((R/'D554-final-host-inventory.json').read_text())
for n,h in inv['hashes'].items():
 p=R/n.removeprefix('resume18/');raw=p.read_bytes()if p.exists()else lzma.decompress(p.with_name(p.name+'.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==h,n
assert '0 loaded units listed'in inv['scopes']
new=[];failed=[];accepted={}
for p in sorted(R.glob('lean-*/receipt/receipt.json')):
 r=json.loads(p.read_text());a=r.get('attempt',0)
 if not(79071<=a<=79096 or 79700<=a<=79799):continue
 assert sha(p.parent.parent/'source.lean')==r['source_sha256']
 assert hashlib.sha256(subprocess.check_output(['git','cat-file','blob',r['project_source_authority']['blob']])).hexdigest()==r['source_sha256']
 assert r['swaps']==0 and r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert json.loads((p.parent.parent/'reservation.json').read_text())['allowed']is True
 assert r['shared_sources_written']is False
 if r['exit_status']==0:
  log=(p.parent/'stdout.log').read_text();assert 'sorryAx'not in log and 'error:'not in log
  axs=re.findall(r'depends on axioms: \[([^\]]*)\]',log);assert axs or 'does not depend on any axioms'in log
  assert all(set(s.replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}for s in axs)
  if r['module']not in accepted or accepted[r['module']]['attempt']<a:accepted[r['module']]=r
 else:failed.append(dict(attempt=a,module=r['module'],exit=r['exit_status'],source_sha256=r['source_sha256'],credit=False))
 new.append({k:r[k]for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','lean_source_revision','source_sha256','print_axioms']})
def passed(module):
 assert module in accepted,module
 assert accepted[module]['source_sha256']==sha(D/'lean'/(module+'.lean')),module
 return accepted[module]['attempt']
updates={
 'qm31_m31_dot':('PV_B3P_DotSource554227','dot_source_link554','DOT-SOURCE-D554.json'),
 'external_linear_lazy':('PV_B3P_ExternalSource554227','external_source_link554','EXTERNAL-SOURCE-D554.json'),
 'expand':('PV_B3P_ExpandSource554227','expand_source_link554','SELECTOR-SOURCE-D554.json'),
 'at_point':('PV_B3P_ConstructorSource554227','statement_constructor49_reference554','SELECTOR-SOURCE-D554.json'),
 'add_path_lanes':('PV_B3P_TerminalSource554227','path_dispatch_source_link554','TERMINAL-SOURCE-D554.json'),
 'add_value_lanes':('PV_B3P_TerminalSource554227','value_source_link554','TERMINAL-SOURCE-D554.json'),
 'semantic_initial_and_absorption':('PV_B3P_TerminalSource554227','initial_absorption_source_link554','TERMINAL-SOURCE-D554.json'),
 'semantic_packed':('PV_B3P_SemanticSource554227','semantic_source_link554','TERMINAL-SOURCE-D554.json'),
 'composition_parts':('PV_B3P_CompositionSource554227','composition_source_link554','TERMINAL-SOURCE-D554.json')}
old=json.loads((R/'PER-FUNCTION-D550.json').read_text())
for row in old['functions']:
 if row['function']not in updates:continue
 m,theorem,dossier=updates[row['function']];a=passed(m)
 row.update(local_body_association='BOUND',route='Lean equality + own-1 structural',theorem='PV_B3P_Association554227.'+theorem,evidence=dossier,accepted_attempt=a,remaining='Local body association at recorded deployed features; complete std/D188/native differentials/matrix/callback and V370/D381/D386 remain explicit')
 if row['function']=='at_point':row['origin_note']='Statement source49 is associated to constructor14 49; distinct terminal57 is separately proved by terminal_constructor57_link554, never by identifying49 with57.'
old['counts']=dict(total=36,bound=36,open=0,direct_extraction=4,Kani=2,Lean_equality_with_structural_source_binding=30)
assert sum(r['local_body_association']=='BOUND'for r in old['functions'])==36
old['new_associations']=list(updates);old['scope']='Local body associations only. Exact deployed dictionary callback hypothesis remains UNDISCHARGED; target not established.'
old['feature_correction']='Fresh specified client metadata excludes optimized-terminal. Selected literal/scaling bodies are bound; no inactive optimized body credited.'
(R/'PER-FUNCTION-D554.json').write_text(json.dumps(old,indent=2)+'\n')
f=json.loads((R/'DEPLOYED-FEATURE-RECHECK-D554.json').read_text());assert f['exit_status']==0
assert f['manifest_sha256']==sha(Path('tools/r1-cost-probe/Cargo.toml'))
node=next(n for n in f['nodes']if n['name']=='aspis-r1-cost-probe');assert 'optimized-terminal'not in node['features']and 'ct-host-prover'in node['features']
for dossier in ['DOT-SOURCE-D554.json','EXTERNAL-SOURCE-D554.json','SELECTOR-SOURCE-D554.json','TERMINAL-SOURCE-D554.json']:
 x=json.loads((R/dossier).read_text());x['status']='BOUND local source associations at recorded features; all consuming focused complete-Result theorems passed. Not whole std/D188/matrix/callback closure.'
 x['accepted_attempts']={name:accepted[m]['attempt']for name,(m,_,d)in updates.items()if d==dossier}
 (R/dossier).write_text(json.dumps(x,indent=2)+'\n')
t=json.loads((R/'TALLY-resume18.json').read_text());assert len(new)==t['lean_attempts']-70
assert inv['extraction_receipts']==8 and inv['kani_receipts']==5
out=dict(target='V244/runjoin op227 OPEN; target not established',before=dict(coverage=27,op227='UNDISCHARGED native callback relation'),after=dict(coverage=36,op227='UNDISCHARGED native callback relation'),coverage=old['counts'],new_lean=new,failed_no_credit=failed,budget=dict(total_remaining_lean=180-t['lean_attempts'],old_resume18_remaining=0,new_block_used=t['lean_attempts']-80,new_block_remaining=180-t['lean_attempts'],next_lean=t['next_unused_id'],new_audits=[79797,79798,79799],unused_old_ids_retired='remaining790xx including79099',extraction=22,kani=25),feature_recheck=dict(sha256=sha(R/'DEPLOYED-FEATURE-RECHECK-D554.json'),selected_host_features=node['features']),premise_changes=dict(removed=[],added=[],weakened=[],T_unchanged=True),host_artifacts_verified=len(inv['hashes']),axioms='accepted new top theorems only propext/Classical.choice/Quot.sound; every failed attempt retained and uncredited',complete_manifest_replay='not run; closure incomplete',checkpoint='context checkpoint, not budget exhaustion')
(R/'verification-summary-D554.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(coverage=old['counts'],accepted=len([r for r in new if r['exit_status']==0]),failed=len(failed),remaining=out['budget'],host_hashes=len(inv['hashes']))))
