"""Pin at most ten independent recovered configurations in each serial scope."""
from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
common=['NML_batch_extract.py','NML_extract.py','NML_NHR_stage.py','NML_STAGER_PIN.json','NML_STAGING_MANIFEST.json','NML_FROZEN_PAYLOAD.json.sha256']
for i,lo in enumerate(range(3,41,10),1):
 a='NML_B%03d'%i;runs=['NML_E%03d'%n for n in range(lo,min(lo+10,41))];spec=dict(scope=a,runs=runs,resource_policy='One capped scope; sequential configurations; unchanged timeout180; no repeated source/command; complete NHR pre/post checks per configuration')
 (E/(a+'_batch.json')).write_text(json.dumps(spec,indent=2)+'\n')
 sources=common+[a+'_batch.json'];collect=[]
 for r in runs:
  c=json.loads((E/(r+'.json')).read_text());sources+=c['sources']+[r+'.json'];collect+=[r,r+'_emitted']
 sources=list(dict.fromkeys(sources));cfg=dict(attempt=a,kind='extract',module='NML_serial_'+runs[0]+'_'+runs[-1],sources=sources,upload=sources+['NML_FROZEN_PAYLOAD.json.xz'],command=['python3','NML_batch_extract.py',a],collect=collect+['NML_TOOL_ATTEMPTS.jsonl'],timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin'},deps_fingerprint={},expected_time='Sequential optimized Charon and Aeneas on ten tiny archived references; per-configuration preflight and GNU time; expected total below unchanged180s. No aggregation/elimination.')
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
print(json.dumps(dict(scopes=4,configurations=38,timeout_each=180,parallel_scopes=1)))
