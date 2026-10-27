from pathlib import Path
import json,hashlib,re,collections,subprocess
E=Path(__file__).resolve().parent;errors=[];receipts=[]
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for p in sorted(E.glob('KSC2_[LR][0-9][0-9][0-9]/receipt.json')):
 d=json.loads(p.read_text());receipts.append(d)
 ad=json.loads((E/(d['attempt']+'-admission.json')).read_text())
 if ad['exit_status']!=0 or ad['allowed'] is not True:errors.append('admission '+d['attempt'])
 if d['limits']!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append('caps '+d['attempt'])
 for name,sha in d['source_hashes'].items():
  q=p.parent/'sources'/name
  if not q.exists() or h(q)!=sha:errors.append('snapshot '+str(q))
 if d['kind']=='lean' and d['exit_status']==0:
  for line in d['print_axioms']:
   if 'depends on axioms:' in line:
    axioms=set(x.strip() for x in line.split('[',1)[1].rstrip(']').split(','))
    if not axioms <= {'propext','Classical.choice','Quot.sound'}:errors.append('axioms '+line)
modules=[];roots=[]
for p in sorted(E.glob('KSC2_*.lean')):
 name='KSC2_generated/'+p.name
 accepted=[d for d in receipts if d['kind']=='lean' and d['exit_status']==0 and d['source_hashes'].get(name)==h(p)]
 if not accepted:errors.append('current source lacks exit0 acceptance '+p.name)
 modules.append(dict(path=p.name,sha256=h(p),accepted_attempts=[d['attempt'] for d in accepted]))
 text=p.read_text();text=re.sub(r'/\-.*?\-/','',text,flags=re.S);text=re.sub(r'--[^\n]*','',text)
 if re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',text):errors.append('forbidden source '+p.name)
 roots.extend('KSC2.'+name for name in re.findall(r'(?m)^theorem (\w+)',text))
final=next(d for d in receipts if d['attempt']=='KSC2_L025')
audited={line.split("'")[1] for line in final['print_axioms']}
if set(roots)!=audited or len(roots)!=41:errors.append('final roots mismatch')
# Preserve full receipt fields, including selected import/Aeneas pins and printed axioms.
(E/'KSC2_attempts.jsonl').write_text(''.join(json.dumps(d,sort_keys=True)+'\n' for d in receipts))
g=json.loads((E/'KSC2_graph.json').read_text());revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
for row in g['manifests']:
 actual=hashlib.sha256(subprocess.check_output(['git','show',revision+':'+row['path']])).hexdigest()
 if actual!=row['sha256']:errors.append('frozen manifest '+row['path'])
if g['lock_sha256']!='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef':errors.append('frozen lock')
old=json.loads((E/'KSC2_R002/KSC2_graph.json').read_text())
if old['metadata_sha256']!=g['metadata_sha256']:errors.append('resolved graph drift')
counts=dict(collections.Counter((d['kind'],d['exit_status']) for d in receipts))
summary=dict(errors=errors,lean_attempts=sum(d['kind']=='lean' for d in receipts),rust_runs=sum(d['kind']=='rust' for d in receipts),kani_runs=0,counts={str(k):v for k,v in counts.items()},current_modules=modules,top_roots=sorted(roots),axiom_audit=final['attempt'],sum_lean_wall_seconds=sum(d['wall_seconds'] for d in receipts if d['kind']=='lean'),max_lean_rss_kib=max(int(d['peak_rss_kib']) for d in receipts if d['kind']=='lean'),sum_rust_wall_seconds=sum(d['wall_seconds'] for d in receipts if d['kind']=='rust'),max_rust_rss_kib=max(int(d['peak_rss_kib']) for d in receipts if d['kind']=='rust'),total_swaps=sum(int(d['swaps']) for d in receipts),frozen_manifest_count=len(g['manifests']),resolved_edges=len(g['validated_edges']),resolved_nodes=g['nodes'],transport_retries=(E/'KSC2_transport.jsonl').read_text().splitlines() if (E/'KSC2_transport.jsonl').exists() else [],final_target={k:final[k] for k in ['attempt','module','command','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']})
(E/'KSC2_VERIFICATION.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['errors','lean_attempts','rust_runs','counts','sum_lean_wall_seconds','max_lean_rss_kib','sum_rust_wall_seconds','max_rust_rss_kib','total_swaps','frozen_manifest_count','resolved_edges']}))
if errors:raise SystemExit(1)
