from gates import call,D,E,H
import subprocess,json
labels={}
labels['fixture_build']=call('native.py',['candidate','{label}','cargo','build','--release','--offline','--locked','-j','4','-p','aspis-r1-cost-probe','--example','prover_rw_gate','--features','optimized-terminal,r1p-check,ct-host-prover'],'build-fixture')
labels['fixture']=call('native.py',['candidate','{label}',D+'/bin/prover_rw_gate',D+'/fixtures-candidate','0','1'],'fixture-fixed')
with (E/'fixture-comparison-driver.log').open('w') as log:
 r=subprocess.run(['ssh',H,'python3 '+D+'/compare-fixtures.py'],stdout=log,stderr=subprocess.STDOUT)
(E/'fixture-labels.json').write_text(json.dumps(labels,indent=2)+'\n')
raise SystemExit(r.returncode)
