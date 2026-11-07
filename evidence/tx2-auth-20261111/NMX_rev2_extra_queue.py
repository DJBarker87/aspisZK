"""Focused next independent steps; stop immediately on a failed predecessor."""
from NMX_formal import *
env=json.loads((E/'NMX_REV2_ENV.json').read_text())
n=600
for m in ['NMX_R2_CloneNative','NMX_R2_ClonePacket','NMX_R2_DeferredValue','NMX_LengthCloneCut','NMX_R2_LengthNative','NMX_R2_CheckpointTail','NMX_R2_CheckpointShape','NMX_R2_StdOps','NMX_R2_ReadonlyNative','NMX_R2_CheckpointCarrier','NMX_R2_CheckpointAfter','NMX_R2_CheckpointPacket','NMX_R2_NativeExecution','NMX_R2_NativeDataBox','NMX_R2_DistinctRange','NMX_R2_DistinctOuter','NMX_R2_DistinctPairwise','NMX_R2_DistinctCanonical','NMX_R2_DistinctMap','NMX_R2_DistinctNative','NMX_R2_Refine','NMX_R2_RSL233Replay','NMX_R2_RSL233Fold','NMX_R2_NativeCommands','NMX_R2_NativeProgram','NMX_R2_NativeSeven','NMX_R2_CountReference','NMX_R2_CountNative','NMX_R2_SevenList','NMX_R2_NativeRoot','NMX_R2_InverseSliceProps','NMX_R2_LaneView','NMX_R2_CanonicalChildren','NMX_R2_NativeCanonical','NMX_R2_StdSource','NMX_R2_ErrorInverse','NMX_R2_InputInjection','NMX_R2_ArgsInjection','NMX_R2_ErrorModelInverse','NMX_R2_AccountReify','NMX_R2_AccountListReify','NMX_R2_ArgsReify','NMX_R2_NativeBounds','NMX_R2_RepresentedFold','NMX_R2_BoxActionObservation','NMX_R2_MasterObservation','NMX_R2_CheckpointObservation']:
 rows=[json.loads(l) for l in (E/'NMX_ATTEMPTS.jsonl').read_text().splitlines()]
 h=sha((E/(m+'.lean')).read_bytes())
 if any(r.get('module')==m and r.get('exit_status')==0 and h in r.get('source_hashes',{}).values() for r in rows):continue
 while (E/('NMX_L'+str(n)+'.json')).exists():n+=1
 r=run('NMX_L'+str(n),'lean',m,env_extra=env);n+=1
 if r['exit_status']:raise RuntimeError('STOP failed predecessor '+m)
