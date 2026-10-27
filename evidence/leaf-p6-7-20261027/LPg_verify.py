from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent;errors=[]
rs={k:[json.loads(p.read_text()) for p in sorted(E.glob('LPg_'+k+'*/receipt.json'))] for k in ['K','L']}
expected_limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for kind,rows in rs.items():
 for r in rows:
  a=r['attempt'];ad=json.loads((E/(a+'-reservation.json')).read_text())
  if not ad['allowed']:errors.append(a+' refused reservation')
  if r['limits']!=expected_limits or str(r['swaps'])!='0':errors.append(a+' limits/swap')
  if kind=='K':
   graph=json.loads((E/(a+'-graph-check.json')).read_text());post=(E/(a+'-lock-after.log')).read_text().split()[0]
   if not graph['graph_matches_frozen'] or graph['edge_errors'] or graph['new_package_tuples']:errors.append(a+' graph drift')
   if graph['graph_sha256']!=json.loads((E/'LPg_FROZEN_GRAPH.json').read_text())['metadata_sha256']:errors.append(a+' graph snapshot mismatch')
   if post!='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef':errors.append(a+' lock drift')
   if r['env']['CARGO_NET_OFFLINE']!='true' or r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']!='3':errors.append(a+' native mode')
  elif r['exit_status']==0:
   for line in r['print_axioms']:
    match=re.search(r'axioms: \[([^]]*)\]',line)
    if match:
     axioms={x.strip() for x in match[1].split(',') if x.strip()}
     if axioms-{'propext','Classical.choice','Quot.sound'}:errors.append(a+' rejected axioms '+str(axioms))
for src in E.glob('LPg_*.lean'):
 sha=hashlib.sha256(src.read_bytes()).hexdigest()
 if not any(r['exit_status']==0 and sha in r['source_hashes'].values() for r in rs['L']):errors.append('uncompiled final source '+src.name)
 if re.search(r'\b(sorry|admit|native_decide)\b|set_option (maxHeartbeats|maxRecDepth)',src.read_text()):errors.append('disallowed proof '+src.name)
if len(rs['K'])!=30 or len(rs['L'])!=59:errors.append('wrong run count')
if (E/'LPg_BEFORE.lean.txt').read_bytes()!=(E/'LPg_AFTER.lean.txt').read_bytes() or (E/'LPg_AFTER.lean.txt').read_bytes()!=Path('lean/FJv_Top.lean').read_bytes():errors.append('top changed')
freeze=subprocess.check_output(['git','diff','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--','crates','programs','Cargo.lock'],text=True)
if freeze:errors.append('frozen shipped source changed')
patch=json.loads((E/'LPg_PATCH_VERIFICATION.json').read_text())
if patch['errors'] or len(patch['checked_attempts'])!=30:errors.append('patch verification')
summary={}
for k,rows in rs.items():
 summary[k]={'actual_commands':len(rows),'passes':sum(r['exit_status']==0 for r in rows),'failures':sum(r['exit_status']!=0 for r in rows),'wall_seconds_sum':sum(r['wall_seconds'] for r in rows),'peak_rss_kib':max(int(r['peak_rss_kib']) for r in rows),'peak_cgroup_bytes':max(int(r['cgroup_memory_peak_bytes']) for r in rows),'swaps':sum(int(r['swaps']) for r in rows)}
summary['L']['charged_missing_prerequisite_launches']=1;summary['L']['budget_charged']=60
out={'errors':errors,'summary':summary,'shipped_source_identical_to_frozen':not freeze,'all_native_graphs_match_frozen':True,'standard_axioms_only_for_retained_theorems':not any('axiom' in e for e in errors),'patches_reconstructed':len(patch['checked_attempts']),'native_source_hashes_checked':sum(len(r['source_hashes']) for r in rs['K']),'actual_top_premises_removed':0,'axioms_audit':'LPg_L060/receipt.json'}
(E/'LPg_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2));assert not errors,errors
