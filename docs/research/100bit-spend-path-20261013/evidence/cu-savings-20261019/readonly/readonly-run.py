from pathlib import Path
import json,hashlib
w=Path('/home/dombarker/project-offloads/aspis-r1-cu-savings-20261019');d=Path('/home/dombarker/project-offloads/aspis-r1-decision1h-20261019');old=Path('/home/dombarker/project-offloads/aspis-r1-worker-b-readonly-runtime-20261019')
pin='4e1fd78fbddb39cb9599de7694105547d8e86e7451f8b9f3e9626789036e8711';assert hashlib.sha256((d/'artifacts/aspis_r1_cost_probe_program.so').read_bytes()).hexdigest()==pin
# Reuse exact original runtime command and environment, changing output directory only.
r=json.loads((old/'runs/readonly-metadata-runtime-1h/receipt.json').read_text()) if (old/'runs/readonly-metadata-runtime-1h/receipt.json').exists() else None
# Original command is retained in governor packet.
g=json.loads((old/'governor/readonly-metadata-runtime-1h-execute.json').read_text());cmd=g['command'];cmd[-1]=str(w/'readonly-results')
plan={'command':cmd,'cwd':str(w/'readonly'),'out':str(w/'runs/readonly-runtime'),'source_revision':'67163f90b driver patch over pinned 32559d source; exact manifest readonly-inputs.json','features':{'driver':['private-leaf-salts','litesvm/persistence-internal'],'SBF':['pool-adapter','private-leaf-salts']},'executed_elf_sha256':pin,'expected_time':'all 13 metadata mutations and two controls, saved canonical transfer fixture; no proof generation','env':{'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin'}}
(w/'readonly-runtime.json').write_text(json.dumps(plan,indent=2))
