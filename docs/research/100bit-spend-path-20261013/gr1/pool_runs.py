import subprocess,pathlib,json,hashlib
r=pathlib.Path('/home/dombarker/project-offloads/aspis-100bit-path-20261013');out=r/'results/gr1-cost-20261013';base=r/'results/100bit-path-20261013'
driver=base/'pool-v0/frozen-driver-copy/pool_gate-v3b'
assert hashlib.sha256(driver.read_bytes()).hexdigest()=='e6af6ed149d0d55cca7680cf7365d0f0c381b20f0b9b95c4d3ae3acc89f9d8f9'
for version,sha,tx in [('v2','c73cfb72515dfd8de491a272999c7a64a2e751f60491da50f952faac4f031d6e','v1'),('v3b','76465ed0432db7cca0559b4f66092a5b5c09d74fb168d29fff7a340bf009ab99','v0')]:
 elf=base/f'pool-adapter-{version}/bin/aspis_r1_cost_probe_program.so';assert hashlib.sha256(elf.read_bytes()).hexdigest()==sha
 for name in ['transfer','withdrawal']:
  for run in range(1,6):
   label=f'pool-{version}-{name}-{run}'
   cmd=['python3','/tmp/gr1-run.py',label,str(r),str(driver),str(base/'pool-input-artifacts/aspis_pool.so'),str(elf),str(base/'pool-input-artifacts/aspis_registry.so'),str(out/(label+'-evidence.json')),str(out/(label+'-task')),name,'success','--reuse',str(base/f'pool-{name}-v1-task/r1-s2-proof.bin'),str(base/f'pool-{name}-v1-task/r1-s2-public-asf8.bin'),'--tx-version',tx]
   subprocess.run(cmd,check=True)
