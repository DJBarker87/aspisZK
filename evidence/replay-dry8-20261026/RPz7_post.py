"""Final concrete transport check, historical statement capture, batched audits."""
from pathlib import Path
import json,math
from RPz7_attempt import run,E,R,T
rs=[json.loads(f.read_text()) for f in E.glob('RPz7_*/receipt.json')]
used=max(int(r['attempt'].split('_')[1]) for r in rs)
assert used==1478,('Review source frontier before allocating audits',used)
# Each call is serial; no scope overlaps the completed source stage.
used+=1
run(f'RPz7_{used:03d}','RPz7_PhaseConsumers',E/'RPz7_PhaseConsumers.lean',['Init','RPz7_S1SemanticCodeVerifyV1','RPz7_S1SemanticCodeFinishV1'])
used+=1
roots=json.loads((R/'evidence/replay-dry6-20261026/RPz5_Rc10-resolution.json').read_text())['roots']
# Historical object cohort only. This never counts as the fresh selected top.
run(f'RPz7_{used:03d}','RPz7_BeforeKernel',E/'RPz7_BeforeKernel.lean',['Init','Lean','Rc10_Top'],roots=roots)
# Audit every accepted new source context exactly once, including generic and
# concrete transport theorems. A failed source is never imported by an audit.
rs=[json.loads(f.read_text()) for f in E.glob('RPz7_*/receipt.json')]
passed=[r['module'] for r in sorted(rs,key=lambda r:int(r['attempt'].split('_')[1])) if r['exit_status']==0 and r['module']!='RPz7_BeforeKernel']
passed=['AspisR1PublicPreparation.Types', 'AspisR1PublicPreparation.Funs', 'ExtractedSemanticRoundsModel', 'ExtractedPublicPreparationSuccess', 'ExtractedPreparationSerializerFields', 'ExtractedPreparationSerializerLoop', 'ExtractedPreparationSerializerWhole', 'ExtractedPublicPreparationBinding', 'ExtractedFirstCallerReachability', 'RepinS6First', 'S6DecoderScopedReuseV1', 'CurrentCompactFirstCompositionV1', 'ExtractedPrefixParseCore', 'ExtractedPreparedModel', 'CurrentPreparedScratchModel', 'CurrentPreparedScratchReachability', 'ExtractedOpeningQueriesModel', 'Query31SourceCalls', 'S2OwnedCurrentCarrierV1', 'S2OwnedSourceInstallationV1', 'S2SdkOwnedInstallationV1', 'S2SdkOwnedReachabilityV1', 'S2SdkOwnedDecodedReuseV1', 'S2SdkProofGateModelV1', 'S2SdkProofPrefixTotalV1', 'S2SdkProofGateTotalV1', 'S2SdkProofComparatorV1', 'S2SdkProofPrefixParentV1', 'S2FrameOperationsTotalV1', 'S2SdkBorrowedEquivalenceV1', 'ExtractedTx1Model']+passed
remaining=1498-used
size=math.ceil(len(passed)/remaining)
groups=[passed[i*len(passed)//remaining:(i+1)*len(passed)//remaining] for i in range(remaining)]
assert all(groups) and len(set(passed))==len(passed)
template=(E/'RPz7_audit-template.txt').read_text()
for ms in groups:
 used+=1;a=f'RPz7_{used:03d}';m=f'RPz7_Audit{used:03d}'
 src=template.replace('@@IMPORTS@@','\n'.join('import '+n for n in ms)).replace('@@SELECTED@@','#[ '+', '.join('`'+n for n in ms)+' ]')
 f=E/(m+'.lean');f.write_text(src)
 d=run(a,m,f,['Init','Lean']+ms)
 if d['exit_status']!=0:raise SystemExit('STOP failed audit partition; isolate without unchanged retry')
print('FINAL ATTEMPT BUDGET',used,flush=True)
