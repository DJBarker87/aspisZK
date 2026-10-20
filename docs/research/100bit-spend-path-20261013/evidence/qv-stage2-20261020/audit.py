"""Audit final source/receipt pins without replaying unchanged Lean targets."""
import json,pathlib,hashlib,re
root=pathlib.Path.cwd(); base=root/'docs/research/100bit-spend-path-20261013'; ev=base/'evidence/qv-stage2-20261020'
data=json.loads((ev/'manifest.json').read_text())
mods=['QvStage2Count','QvStage2Bridge','QvStage2Privacy','QvStage2Retained']
final=[]
for mod in mods:
 r=next(x for x in reversed(data['attempts']) if x['module']==mod)
 p=root/r['source']; assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256']
 assert r['exit_status']==0
 text=r['axioms_output']; assert 'sorryAx' not in text and 'error:' not in text
 reports=re.findall(r"'([^']+)' (depends on axioms:\s*\[[^\]]*\]|does not depend on any axioms)",text,re.S)
 assert len(reports)==len(re.findall(r'^#print axioms ',p.read_text(),re.M))
 for name,report in reports:
  if '[' in report:
   assert set(x.strip() for x in report.split('[',1)[1].split(']')[0].split(',')) <= {'propext','Classical.choice','Quot.sound'}
 for imp in r['direct_imports']:
  q=pathlib.Path(imp['object_path']); assert hashlib.sha256(q.read_bytes()).hexdigest()==imp['object_sha256']
 assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b',re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S))
 final.append({'module':mod,'source_sha256':r['source_sha256'],'exit_status':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_rss_bytes':r['peak_rss_bytes'],'process_swap_count':r['process_swap_count'],'axiom_reports':[{'theorem':n,'report':v} for n,v in reports]})
out={'schema':'qv-stage2-final-receipt-audit-v1','final_targets':final,'total_theorems':sum(len(x['axiom_reports']) for x in final),'wall_seconds':sum(x['wall_seconds'] for x in final),'peak_rss_bytes':max(x['peak_rss_bytes'] for x in final),'process_swap_count':sum(x['process_swap_count'] for x in final),'historical_attempt_count':len(data['attempts'])-len(final),'status':'pass'}
(ev/'audit.json').write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps({k:v for k,v in out.items() if k!='final_targets'}))
