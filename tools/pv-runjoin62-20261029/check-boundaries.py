from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin62-20261029';base='474daaf0f1857fc01175426409f88c098716f659';prefix='docs/research/v8-r0-zk-20261009/lean/R1Z/'
files=['PV_RunJoin_PublishSkeleton54.lean','PV_RunJoin_PublishSkeleton57.lean','PV_RunJoin_PublishContext57.lean','PV_RJN_NodeContext.lean','PV_RunJoin_ActualProvenance60.lean','PV_RunJoin_CaptureFactorSource60.lean','PV_RunJoin_CapturedTransport60.lean','PV_RunJoin_ActualRun59.lean','PV_RunJoin_NativeOriginalPublication60.lean']
checks=[]
for n in files:
 path=prefix+n;b=subprocess.check_output(['git','show',base+':'+path]);now=(R/path).read_bytes();checks.append(dict(path=path,before=hashlib.sha256(b).hexdigest(),after=hashlib.sha256(now).hexdigest(),unchanged=b==now))
protected=subprocess.check_output(['git','diff','--name-only',base,'--','crates','programs','tools/r1-cost-probe','design/PRIVACY-LEDGER-20261026.md',prefix+'PV_RJDec*',prefix+'PV_OWN*',prefix+'PV_RJQ*',prefix+'PV_RJN*'],text=True).splitlines();assert not protected;assert all(v['unchanged'] for v in checks)
(E/'boundaries.json').write_text(json.dumps(dict(entry=base,checks=checks,protected_changes=protected,rows_removed=[],endpoint_premises_changed=0,keys_changed=False),indent=2)+'\n')
