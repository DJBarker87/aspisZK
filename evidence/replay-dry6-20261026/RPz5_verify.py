"""Read-only final source/receipt/object consistency check; no Lean invocation."""
from pathlib import Path
import json,hashlib,subprocess,collections
E=Path(__file__).resolve().parent;R=E.parents[1];H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-replay-dry-20261026'
g=json.loads((E/'RPz5_source-plan.json').read_text());state=json.loads((E/'RPz5_state.json').read_text())['state'];rs=sorted((json.loads(f.read_text()) for f in E.glob('RPz5_*/receipt.json')),key=lambda r:int(r['attempt'].split('_')[1]));errors=[];prior={}
for directory in ['replay-dry2-20261026','replay-dry3-20261026','replay-dry4-20261026','replay-dry5-20261026','replay-dry6-20261026']:
 for f in sorted((R/'evidence'/directory).glob('RPz*_*/receipt.json'),key=lambda p:p.stat().st_mtime):
  r=json.loads(f.read_text());m=r['module'];x=g['modules'].get(m,{})
  if directory=='replay-dry6-20261026' and 57<=int(r['attempt'].split('_')[1])<=88:continue
  if r['exit_status']==0 and list(r.get('source_hashes',{}).values())==[x.get('sha256')]:prior[m]={'receipt_path':str(f.relative_to(R)),**r}
green={};missing_receipt=[]
for m in g['order']:
 if state.get(m)!='passed':continue
 if m not in prior:missing_receipt.append(m);continue
 bad=[n for n in g['modules'][m]['imports'] if g['modules'][n]['kind']!='trusted-library' and n not in green]
 if bad:errors.append({'consumer':m,'non_green_predecessors':bad})
 green[m]=prior[m]
edges=[]
for r in list(green.values())+[r for r in rs if r['exit_status']==0 and r['module'].startswith('RPz5_Audit')]:
 for n,pin in r['deps_fingerprint'].get('selected_objects',{}).items():edges.append({'consumer':r['module'],'dependency':n,**pin})
overlay=json.loads((E/'RPz5_overlay-base.json').read_text())
for line in (E/'RPz5_overlay-additions.jsonl').read_text().splitlines():overlay.update(json.loads(line)['artifacts'])
paths=sorted({e['path'] for e in edges});headers=json.loads((R/'evidence/replay-dry5-20261026/RPz4_coherent-headers.json').read_text())['modules'];lib=json.loads((R/'evidence/replay-dry5-20261026/RPz4_AeneasMeta-base.json').read_text())['artifacts']
payload='''from pathlib import Path
import json,hashlib,subprocess
B=Path(%r);paths=json.loads(%r)
def pin(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1024*1024),b''):h.update(c)
 return {'sha256':h.hexdigest(),'bytes':p.stat().st_size}
actual={f:pin(Path(f)) if Path(f).is_file() else None for f in paths}
objects={str(p.relative_to(B)):pin(p) for p in (B/'RPz5_objects').rglob('*') if p.is_file()}
live=[]
for line in subprocess.check_output(['ps','-eo','pid,comm,args'],text=True).splitlines()[1:]:
 fields=line.split(None,2)
 if len(fields)==3 and fields[1] in ['python3','lean','lake'] and 'RPz5_' in fields[2]:live.append(line)
print(json.dumps({'actual':actual,'objects':objects,'live':live,'default_lake_objects_exist':(B/'.lake/build/lib/lean').exists(),'overlay_link_targets':{f:str(Path(f).readlink()) if Path(f).is_symlink() else None for f in json.loads(%r)}}))
'''%(B,json.dumps(sorted(set(paths)|{v['path'] for v in headers.values()}|set(lib)|set(overlay))),json.dumps(list(overlay)))
r=subprocess.run(['ssh',H,'python3 -'],input=payload,text=True,capture_output=True);assert r.returncode==0,r.stderr;host=json.loads(r.stdout)
mismatches=[e for e in edges if host['actual'][e['path']]!={k:e[k] for k in ['sha256','bytes']}]
header_drift=[{'module':n,**v,'actual':host['actual'][v['path']]} for n,v in headers.items() if host['actual'][v['path']]!={k:v[k] for k in ['sha256','bytes']}]
lib_drift=[{'path':p,**v,'actual':host['actual'][p]} for p,v in lib.items() if host['actual'][p]!={k:v[k] for k in ['sha256','bytes']}]
overlay_drift=[{'path':p,**v,'actual':host['actual'][p],'actual_link_target':host['overlay_link_targets'][p]} for p,v in overlay.items() if host['actual'][p]!={k:v[k] for k in ['sha256','bytes']} or host['overlay_link_targets'][p]!=v['target']]
source_bad=[m for m in g['order'] if hashlib.sha256((R/g['modules'][m]['source']).read_bytes()).hexdigest()!=g['modules'][m]['sha256']]
ids=[int(r['attempt'].split('_')[1]) for r in rs];ready=[m for m in g['order'] if state.get(m) not in ['passed','failed'] and all(g['modules'][n]['kind']=='trusted-library' or state.get(n)=='passed' for n in g['modules'][m]['imports'])]
if missing_receipt:errors.append('passed modules without matching source receipt')
if mismatches:errors.append('stale direct dependency object')
if source_bad:errors.append('selected source drift')
if lib_drift:errors.append('pinned AeneasMeta library drift')
if overlay_drift:errors.append('job namespace view drift')
if host['live']:errors.append('live job compiler/runner')
if host['default_lake_objects_exist']:errors.append('unexpected default Lake object directory')
if ids!=list(range(1,len(rs)+1)):errors.append('attempt numbers not contiguous')
if len(rs)>1500:errors.append('budget exceeded')
audit_file=E/'RPz5_axiom-audit.json'
if audit_file.exists():
 a=json.loads(audit_file.read_text())
 if a['audit_completion_errors'] or a['source_import_header_mismatches'] or a['passed_modules_missing_audit'] or a['duplicate_owner_name_pairs'] or a['declaration_queries']!=a['raw_print_results']:errors.append('axiom audit coverage/header mismatch')
tracked_changed=subprocess.check_output(['git','diff','--name-only',json.loads((E/'RPz5_PROVENANCE.json').read_text())['revision']],cwd=R,text=True).splitlines();outside=[p for p in tracked_changed if not p.startswith('evidence/replay-dry6-20261026/')]
if outside:errors.append('change outside authorized evidence directory')
out={'attempts':len(rs),'attempt_numbers_contiguous':ids==list(range(1,len(rs)+1)),'passed_attempts':sum(r['exit_status']==0 for r in rs),'failed_attempts':[{'attempt':r['attempt'],'module':r['module'],'exit':r['exit_status']} for r in rs if r['exit_status']],'obsolete_probe_attempts':[r['attempt'] for r in rs if 57<=int(r['attempt'].split('_')[1])<=88],'green_module_contexts':len(green),'green_receipt_paths':{m:r['receipt_path'] for m,r in green.items()},'missing_matching_receipts':missing_receipt,'direct_edges_checked':len(edges),'unique_direct_object_paths':len(paths),'direct_object_mismatches':mismatches,'historical_header_object_drift':header_drift,'AeneasMeta_library_drift':lib_drift,'overlay_artifacts_checked':len(overlay),'overlay_drift':overlay_drift,'source_hash_mismatches':source_bad,'output_object_inventory':host['objects'],'live_job_processes':host['live'],'default_lake_object_directory_exists':host['default_lake_objects_exist'],'ready_unattempted':ready,'frontier':json.loads((E/'RPz5_frontier.json').read_text()),'selected_source_count':len(g['order']),'unresolved_names':g['unresolved'],'wall_seconds_sum':sum(r['wall_seconds'] for r in rs),'peak_rss_kib':max(int(r['peak_rss_kib']) for r in rs),'swaps':sum(int(r['swaps']) for r in rs),'outside_authorized_path':outside,'errors':errors,'qualification':'Metadata/hash consistency only. Historical header drift is reported separately and is not accepted as a replacement input. No full top, joint non-vacuity or source-to-ELF claim.'}
(E/'RPz5_final-verification.json').write_text(json.dumps(out,indent=2)+'\n');print({k:out[k] for k in ['attempts','green_module_contexts','direct_edges_checked','unique_direct_object_paths','errors','historical_header_object_drift']})
