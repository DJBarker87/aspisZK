from gates import call,D,E,H
import json,subprocess
labels={}
for side in ['baseline','candidate']:
 script='baseline/native.py' if side=='baseline' else 'native.py'
 root=D+'/baseline' if side=='baseline' else D
 labels[side+'_build']=call(script,['candidate','{label}','cargo','build','--release','--offline','--locked','-j','4','-p','aspis-r1-cost-probe','--example','prover_rw_gate','--features','optimized-terminal,r1p-check,ct-host-prover'],'build-fixture-'+side)
 labels[side+'_run']=call(script,['candidate','{label}',root+'/bin/prover_rw_gate',root+'/fixtures-candidate','0','1'],'fixture-fixed-'+side)
(E/'fixture-labels.json').write_text(json.dumps(labels,indent=2)+'\n')
r=subprocess.run(['ssh',H,'python3 '+D+'/compare-fixtures.py'],stdout=(E/'fixture-comparison-driver.log').open('w'),stderr=subprocess.STDOUT)
raise SystemExit(r.returncode)
