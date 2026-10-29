from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin63-20261029'
accepted={v['module']:v for q in sorted(E.glob('modules-*.json')) for v in json.loads(q.read_text()) if v['accepted']}
rows=[]
for p in sorted((R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_RunJoin_*63.lean')):
 m='R1Z.'+p.stem;h=hashlib.sha256(p.read_bytes()).hexdigest();v=accepted.get(m)
 text=re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S);text=re.sub(r'--[^\n]*','',text)
 bad=re.findall(r'\b(?:sorry|admit|axiom|native_decide)\b|set_option\s+(?:maxRecDepth|maxHeartbeats)',text)
 assert not bad,(m,bad)
 rows.append(dict(module=m,sha256=h,accepted_current_source=bool(v and v['source_sha256']==h),receipt_source_sha256=v['source_sha256'] if v else None))
(E/'source-status.json').write_text(json.dumps(rows,indent=2)+'\n')
print('current source accepted',sum(v['accepted_current_source'] for v in rows),'of',len(rows),'forbidden proof text absent')
print('unaccepted',[v['module'] for v in rows if not v['accepted_current_source']])
