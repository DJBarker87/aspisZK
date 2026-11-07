"""Focused next independent steps; stop immediately on a failed predecessor."""
from NMX_formal import *
env=json.loads((E/'NMX_REV2_ENV.json').read_text())
n=600
for m in ['NMX_R2_CloneNative','NMX_R2_ClonePacket','NMX_LengthCloneCut','NMX_R2_LengthNative','NMX_R2_CheckpointShape','NMX_R2_StdOps','NMX_R2_ReadonlyNative','NMX_R2_DistinctRange','NMX_R2_DistinctOuter','NMX_R2_DistinctPairwise','NMX_R2_DistinctCanonical','NMX_R2_Refine','NMX_R2_RSL233Replay','NMX_R2_RSL233Fold']:
 rows=[json.loads(l) for l in (E/'NMX_ATTEMPTS.jsonl').read_text().splitlines()]
 h=sha((E/(m+'.lean')).read_bytes())
 if any(r.get('module')==m and r.get('exit_status')==0 and h in r.get('source_hashes',{}).values() for r in rows):continue
 while (E/('NMX_L'+str(n)+'.json')).exists():n+=1
 r=run('NMX_L'+str(n),'lean',m,env_extra=env);n+=1
 if r['exit_status']:raise RuntimeError('STOP failed predecessor '+m)
