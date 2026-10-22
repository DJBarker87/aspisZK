#!/usr/bin/env python3
"""Same deterministic transfer/withdrawal fixtures, two separately pinned binaries."""
from pathlib import Path
import os,subprocess,hashlib,json
R=Path(__file__).resolve().parents[2];H=R.parent
results=[]
for mode,src,features in [('baseline',H/'baseline-src','optimized-terminal,r1p-check'),('ct',R,'optimized-terminal,ct-host-prover')]:
 env=dict(os.environ,CT_EXPECTED='Optimized native compilation only; subsequent run measures two proof generations and P_R1 elimination')
 runner=src/'tools/ct-kernels-20261022/run-host.py'
 subprocess.run(['python3',str(runner),mode+'-timed-build','cargo','build','--release','-p','aspis-r1-cost-probe','--example','ct_fixture_gate','--features',features,'-j','4','--locked'],env=env,check=True)
 binary=H/'native-artifacts'/('timed-'+mode)
 binary.write_bytes((H/'target/release/examples/ct_fixture_gate').read_bytes());binary.chmod(0o755)
 output=H/('fixtures-timed-'+mode)
 env['CT_EXPECTED']='Single-sample fixture measurement: two full proof generations including P_R1 elimination; no compilation'
 subprocess.run(['python3',str(runner),mode+'-timed-run',str(binary),str(output)],env=env,check=True)
 results.append(dict(mode=mode,binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),binary_bytes=binary.stat().st_size,features=features,files={str(p.relative_to(output)):hashlib.sha256(p.read_bytes()).hexdigest() for p in output.rglob('*') if p.is_file()}))
 (R/'fixture-identities.json').write_text(json.dumps(results,indent=2)+'\n')
for name in ['S2-transfer','S2-withdrawal']:
 a=H/'fixtures-timed-baseline'/name/'proof.bin'; b=H/'fixtures-timed-ct'/name/'proof.bin'
 assert a.read_bytes()==b.read_bytes(),name
print('Transfer and withdrawal proof bytes are identical')
