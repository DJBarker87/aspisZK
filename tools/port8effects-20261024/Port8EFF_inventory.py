#!/usr/bin/env python3
"""Read-only inventory and pinned source assessment; no extraction or build."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean';E=R/'evidence/port8effects-20261024'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
adapt=R/'evidence/verifier-top-20261023/generated-complete/adaptation.json'
ext=R/'evidence/verifier-top-20261023/generated-complete/VTop_Stages/FunsExternal_Template.lean.txt'
names=json.loads(adapt.read_text())['operations']; body={3,4,5,6,7,8,9,10,11,12,17,18,19}
producers={3:[],4:[],5:['Port3_NativeBatchBody','Port3_BatchStage','Port4B_BatchJoin'],6:['Port3_NativeQueryBody','Port3_QueryStage'],7:[],8:['CheckpointBytes5Writer','Port3_CheckpointInstall'],9:['Port3_FlushInstall'],10:['Port3_NativePendingInstall'],11:['Port3_NativeGeometryBody','Port3_GeometryStage'],12:['Port3_Constructor'],17:[],18:['Port4A_NativeReader','Port4A_ReaderNormalize','CheckpointBytes5Resume','Port6CK_Ops','Port6CK_Reader'],19:['Port3_FinishStage']}
rows=[];pins={}
for block in ext.read_text().split('/--')[1:]:
 m=re.search(r'axiom ([\w.]+)',block)
 if not m or m[1] not in names:continue
 op=int(names[m[1]][2:])
 if op not in body:continue
 src=re.search(r"Source: '([^']+)', lines ([^\n]+)",block)
 path=R/src[1];pins[src[1]]={'sha256':sha(path),'bytes':path.stat().st_size}
 ps=[str((L/(n+'.lean')).relative_to(R)) for n in producers[op] if (L/(n+'.lean')).is_file()]
 rows.append({'id':op,'operation':m[1],'rust_source':src[1],'emitted_lines':src[2], 'existing_producers':ps,'status': 'Session A source-effect producer pending; not discharged' if op in {7,17} else ('installed here; existing source/leaf/ABI interpretations retained' if op in {8,18} else 'existing source/value producer; not installed as effects by this job')})
assert len(rows)==13
for p in [adapt,ext,*[L/(n+'.lean') for ns in producers.values() for n in ns if (L/(n+'.lean')).is_file()],L/'VTop_OracleStages.lean',L/'VTop_OracleCode.lean']:
 pins[str(p.relative_to(R))]={'sha256':sha(p),'bytes':p.stat().st_size}
old=json.loads((R/'evidence/verifier-top-20261023/target.json').read_text())
assessment={p:{'current':pins[p]['sha256'],'historical':v['sha256'],'unchanged':pins[p]['sha256']==v['sha256']} for p,v in old['files'].items() if p in pins}
assert all(x['unchanged'] for x in assessment.values())
(E/'source-inventory.json').write_text(json.dumps({'revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'operations':rows,'pins':pins,'reused_source_assessment':assessment,'scope':'Static source assessment only; historical cached evidence is not an ELF identity gate. External axiom template is inventory data, never imported.'},indent=2)+'\n')
print('Pinned 13 body operations; no shipped source changes')
