from pathlib import Path
import subprocess,os,json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-n7-20261027');R=H/'patched'
# Expected time: optimized helper linking, then exactly two transfer/withdrawal
# pairs through the actual devnet_spend binaries; time in proof/P_R1 generation.
helper=R/'tools/r1-cost-probe/src/bin/pv_n7_requests.rs'
helper.write_bytes((H/'request-fixture.rs').read_bytes())
subprocess.run(['cargo','build','--manifest-path','tools/r1-cost-probe/Cargo.toml','--release','--offline','--locked','-j','4','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bin','pv_n7_requests'],cwd=R,check=True)
subprocess.run([str(H/'target/release/pv_n7_requests'),str(H/'fixtures')],check=True)
subprocess.run(['cc','-shared','-fPIC','-O2','-o',str(H/'fixture-entropy.so'),str(H/'fixture-entropy.c'),'-ldl'],check=True)
rows=[]
for n in range(2):
 q=json.loads((H/'fixtures'/f'request-{n}.json').read_text());proofs={}
 for which in ['base','patched']:
  directory=H/'fixtures'/f'{which}-{n}'
  request={**q,'proof_dir':str(directory)}
  (H/'fixtures'/f'{which}-{n}-request.json').write_text(json.dumps(request,indent=2)+'\n')
  env=dict(os.environ,LD_PRELOAD=str(H/'fixture-entropy.so'))
  r=subprocess.run([str(H/('devnet_spend-'+which))],input=json.dumps(request),text=True,capture_output=True,env=env)
  (H/'evidence'/f'{which}-{n}-stdout.json').write_text(r.stdout)
  (H/'evidence'/f'{which}-{n}-stderr.log').write_text(r.stderr)
  assert r.returncode==0,(which,n,r.stderr)
  assert r.stderr.count('N7_FIXTURE_ENTROPY_64')>=1,'hook was not reached'
  proofs[which]={'proof.bin':(directory/'proof.bin').read_bytes(),'statement.bin':(directory/'statement.bin').read_bytes()}
  print(which,n,len(proofs[which]['proof.bin']),flush=True)
 row={'note':n,'withdrawal':n==1,'request_sha256':hashlib.sha256((H/'fixtures'/f'request-{n}.json').read_bytes()).hexdigest(),'files':{}}
 for f in ['proof.bin','statement.bin']:
  a,b=proofs['base'][f],proofs['patched'][f];assert a==b,(n,f)
  row['files'][f]=dict(byte_identical=True,sha256=hashlib.sha256(a).hexdigest(),bytes=len(a))
 a=json.loads((H/'evidence'/f'base-{n}-stdout.json').read_text());b=json.loads((H/'evidence'/f'patched-{n}-stdout.json').read_text())
 # Wall time is deliberately not compared; all operational outputs must match.
 del a['prove_wall_seconds'];del b['prove_wall_seconds'];assert a==b
 rows.append(row)
(H/'evidence/fixtures.json').write_text(json.dumps(dict(actual_binaries=True,entropy='TEST-ONLY LD_PRELOAD deterministic 64-byte attempt fills; public selected proof accounts fixed; not production entropy',rows=rows,print_axioms='N/A'),indent=2)+'\n')
