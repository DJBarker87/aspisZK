"""Pin used executable artifacts by SHA-256 + size, never export binaries."""
import hashlib,json,sys
from pathlib import Path
H=Path(sys.argv[1]);paths=[H/'artifacts/pool_gate',H/'artifacts/pool_gate_trace',H/'driver-target/release/component_checks']
for name,so in [('verifier','aspis_r1_cost_probe_program.so'),('pool','aspis_pool.so'),('verifier-profiling','aspis_r1_cost_probe_program.so'),('verifier-debuglines','aspis_r1_cost_probe_program.so')]:
 paths += [H/'artifacts'/name/so,H/'artifacts'/name/'linked.elf']
paths += [Path('/home/dombarker/project-offloads/active-mask-basis-sbf-20261017/artifacts/aux-current/registry/aspis_registry.so')]
rows=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in paths]
assert rows[3]['sha256']=='8cf8d84ed0fe340a190b4f40a9f953f0e0523370299ba3ec8bbed9d65b88ace3'
assert rows[5]['sha256']=='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'
(H/'artifacts.json').write_text(json.dumps(rows,indent=1))
(H/'artifacts-sha256.txt').write_text('Target source revision e90cf2f800f7177e5cca47aa7e5ba59a940130dd\nSBF 3.1.13 / platform-tools v1.52; optimized -j 4; LiteSVM 0.16.0 / Agave 4.2.1.\nNo executable artifacts committed.\n'+'\n'.join(f"{r['sha256']}  {r['bytes']} bytes  {r['path']}" for r in rows)+'\n')
print('Pinned',len(rows),'artifacts')
