#!/usr/bin/env python3
"""Measure a changed stage once; compare full proof/public bytes with retained
baseline fixture files. Never repeat the unchanged baseline proof generation.
"""
from pathlib import Path
import os,subprocess,hashlib,json,sys
R=Path(__file__).resolve().parents[2];H=R.parent
stage=sys.argv[1]
assert stage.replace('-','').isalnum()
runner=R/'tools/ct-kernels-20261022/run-host.py'
env=dict(os.environ,CT_EXPECTED='Optimized native compilation only; runtime proof generation and P_R1 elimination follow in a separate scope')
subprocess.run(['python3',str(runner),stage+'-fixture-build','cargo','build','--release','-p','aspis-r1-cost-probe','--example','ct_fixture_gate','--features','optimized-terminal,ct-host-prover','-j','4','--locked'],env=env,check=True)
binary=H/'native-artifacts'/stage
assert not binary.exists()
binary.write_bytes((H/'target/release/examples/ct_fixture_gate').read_bytes());binary.chmod(0o755)
out=H/('fixtures-'+stage)
env['CT_EXPECTED']='Single-sample measurement: two full proof generations including P_R1 checker elimination; no compilation'
subprocess.run(['python3',str(runner),stage+'-fixture-run',str(binary),str(out)],env=env,check=True)
rows=[]
for name in ['S2-transfer','S2-withdrawal']:
 for file in ['proof.bin','public.bin']:
  assert (out/name/file).read_bytes()==(H/'fixtures-timed-baseline'/name/file).read_bytes(),(name,file)
 r=json.loads((out/name/'fixture.json').read_text());rows.append(r)
result=dict(stage=stage,baseline='retained fixtures-timed-baseline; unchanged source; no repeated baseline run',binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),binary_bytes=binary.stat().st_size,features='optimized-terminal,ct-host-prover',proof_and_public_byte_identity=True,fixtures=rows)
(R/(stage+'-fixture-identities.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
