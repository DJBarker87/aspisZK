"""Focused immutable source capture only. Never reads worker worktrees/caches."""
import hashlib,json,pathlib,subprocess
OUT=pathlib.Path('evidence/port30join-20261025/sources')
A='d346dc7cb7232f12c4ff930d1e2db320bdc101d9'
P='docs/research/100bit-spend-path-20261013/'
groups=[(A,P+'lean-candidates/s126-caller-boundary-20261021/',[
'S1SdkSelectedSemanticTraceV1','S6SdkSelectedSemanticCallerV1','S6SdkSelectedSemanticCutV1',
'S6SdkSourceCutTypesV1','S6SdkOriginalObjectCallerV1','S6SdkFirstObjectEquivalenceV1',
'S6SdkSourceCutReuseV1','S6SdkEnclosingCutsV1','S1SdkPreparedChallengeRangesV1',
'S1SemanticFinishModelV1','S1NativePrepareBuffersV1','S6SdkDependencyFactorV1']),
('904745b496',P+'lean/',[
'S2W_D189Consolidation','S2W_D189Wrappers','S2W_D189Entry','S2W_TrustedStd',
'S2W_ExtractionBoundary','S2W_DigestExtraction','S2W_NativeConsolidation',
'S2TrustedSdkBorrow','S2W_ExpandedChildren','S2W_ScheduledConsolidation',
'S2W_TraceSplice','OraclePortCompactDraft','S2W_FirstOccurrence','S2W_OuterOccurrences','ImportUnionNamedDiscriminant',
'S2W_InputSchedule','S2W_AuthenticatedInputs','S2W_ChildJoins',
'S8OwnedP6/Types','S8OwnedP6/Funs'])]
rows=[]
for rev,base,names in groups:
 for n in names:
  path=base+n+'.lean'
  r=subprocess.run(['git','show',rev+':'+path],capture_output=True)
  row={'revision':rev,'path':path,'exit':r.returncode}
  if r.returncode==0:
   dst=OUT/(rev[:10]+'-'+n.replace('/','-')+'.lean.txt')
   dst.parent.mkdir(parents=True,exist_ok=True); dst.write_bytes(r.stdout)
   row.update(snapshot=str(dst),bytes=len(r.stdout),sha256=hashlib.sha256(r.stdout).hexdigest())
  else: row['error']=r.stderr.decode().strip()
  rows.append(row)
pathlib.Path('evidence/port30join-20261025/source-pins.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps({'captured':sum(r['exit']==0 for r in rows),'absent':[r['path'] for r in rows if r['exit']]}))
