from gates import call,D,E,H
import json
labels={}
labels['client']=call('native.py',['candidate','{label}','cargo','build','--manifest-path','tools/r1-cost-probe/Cargo.toml','--release','--offline','--locked','-j','4','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bin','devnet_spend'],'build-client')
labels['route']=call('native.py',['candidate','{label}','python3',D+'/binary-route.py'],'route-client')
(E/'client-labels.json').write_text(json.dumps(labels,indent=2)+'\n')
