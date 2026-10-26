"""Read immutable git objects only; capture recount inputs without builds."""
from pathlib import Path
import subprocess,json,hashlib
OUT=Path(__file__).resolve().parent
R='docs/research/v8-r0-zk-20261009/lean/R1Z/'
H='docs/research/100bit-spend-path-20261013/evidence/'
def git(*a): return subprocess.check_output(['git',*a])
pins=json.loads((OUT/'pins.json').read_text())
spec={
'rw':[H+'prover-rw-20261023/success-p8/README.md'],
'dict':['design/PDict_20261026.md',H+'prover-dict-20261026/reach7/REACHABILITY.md',H+'prover-dict-20261026/reach7/20701-receipt.json',H+'prover-dict-20261026/reach7/lean-summary.json']+[R+n+'.lean' for n in ['PDict_CurrentCaller','PDict_PureDictionary','PDict_CodecDictionary','PDict_ReachCaller','PDict_ReachErase','PDict_CurrentRetention','PDict_PureSource','PDict_ConstantsSource','PDict_CodecSource','PDict_FormatterReserveFallible']],
'runjoin':[R+n+'.lean' for n in ['PV_RunJoin_Endpoint','PV_RunJoin_Source','PV_RunJoin_CanonicalFixtures','PV_RunJoin_FixtureFibres','PV_RunJoin_NativeRepeat','PV_RunJoin_Coupling']],
'l1':[R+'PV_L1_Premises.lean'],
'l2':[R+n+'.lean' for n in ['PV_L2_Premises','PV_L2_InversionQ','PV_L2_InversionPole','PV_L2_HeadlineJoint']],
'client':['evidence/pv-client-20261026/runtime-02-public/acceptance.json','evidence/pv-client-20261026/runtime-bundle.json'],
}
# Also retain every source defining a baseline row, plus concrete model producers.
baseline=json.loads(Path('evidence/privacy-ledger-20261026/premises.json').read_text())
spec['research']=sorted(set(x['definition'].split('#')[0] for x in baseline)|{R+n+'.lean' for n in ['ProverCommitAdmittedEndpoint','PrivacyR1Headline','PrivacyR1AcctBasis','ProverCommitOwnedEndpoint','BuilderAdmissionCanonical','BuilderRecordCanonical']})
pins['research']={'ref':'HEAD','revision':git('rev-parse','HEAD').decode().strip()}
manifest=[]
for label,paths in spec.items():
 rev=pins[label]['revision']
 for path in paths:
  result=subprocess.run(['git','show',rev+':'+path],capture_output=True)
  entry={'label':label,'revision':rev,'path':path,'exit':result.returncode}
  if result.returncode==0:
   target=OUT/'inputs'/label/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(result.stdout)
   entry.update(local=str(target.relative_to(OUT)),sha256=hashlib.sha256(result.stdout).hexdigest(),bytes=len(result.stdout))
  else: entry['error']=result.stderr.decode().strip()
  manifest.append(entry)
(OUT/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(OUT/'pins.json').write_text(json.dumps(pins,indent=2)+'\n')
print(json.dumps({'captured':sum(x['exit']==0 for x in manifest),'missing':[(x['label'],x['path']) for x in manifest if x['exit']]}))
