#!/usr/bin/env python3
import pathlib,re,json,hashlib,subprocess
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026';lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
a=[json.loads(x) for x in (e/'resume9-attempts.jsonl').read_text().splitlines()];rows=[]
base='3873ce854e'
paths=subprocess.check_output(['git','diff','--name-only',base,'--',str(lean.relative_to(root))],cwd=root,text=True).splitlines()
for f in paths:
 p=root/f
 if p.suffix!='.lean':continue
 s=p.read_text();sha=hashlib.sha256(p.read_bytes()).hexdigest();forbidden=re.findall(r'(?m)^\s*(?:axiom|opaque|unsafe|sorry|admit)\b|\b(?:native_decide|implemented_by|maxRecDepth|maxHeartbeats)\b',s)
 matches=[r for r in a if r['module']=='R1Z/'+p.stem and r['source_sha256']==sha and r.get('accepted')]
 rows.append(dict(path=f,sha256=sha,forbidden=forbidden,accepted_attempts=[r['attempt'] for r in matches]))
f='docs/research/v8-r0-zk-20261009/lean/R1Z/PV_Src_NativePremises.lean';original=subprocess.check_output(['git','show',base+':'+f],cwd=root);current=(root/f).read_bytes()
out=dict(new_sources=rows,original_deployed_premises_byte_equal=current==original,deployed_premises_sha256=hashlib.sha256(current).hexdigest(),shipped_source_diff=subprocess.check_output(['git','diff','--name-only',base,'--','crates','programs'],cwd=root,text=True).splitlines())
(e/'resume9-new-source-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(dict(sources=len(rows),uncompiled=sum(not r['accepted_attempts'] for r in rows),forbidden=sum(bool(r['forbidden']) for r in rows),premises_unchanged=current==original,shipped_changes=out['shipped_source_diff']))
