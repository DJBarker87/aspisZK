from pathlib import Path
import json,shutil
w=Path('/home/dombarker/project-offloads/aspis-r1-cu-savings-20261019');d=Path('/home/dombarker/project-offloads/aspis-r1-decision1h-20261019');r=json.loads((w/'runs/c1-sbf/receipt.json').read_text());assert r['exit_status']==0
out=w/'candidate1-stack';out.mkdir();shutil.copy2(d/'sbf-target/sbpf-solana-solana/release/aspis_r1_cost_probe_program.so',out/'linked.elf');shutil.copy2(w/'candidate1-artifacts/aspis_r1_cost_probe_program.so',out/'stripped.so');(out/'build.log').write_bytes((w/'runs/c1-sbf/stdout.log').read_bytes()+(w/'runs/c1-sbf/stderr.log').read_bytes())
base={'source_revision':'3ab4faf7f5b488a0c82720717656a0ebf4c46efa','features':['pool-adapter','private-leaf-salts'],'cwd':str(w/'sbf'),'expected_time':'ELF inspection or saved-fixture SBF replay, no proof generation'}
(w/'stack.json').write_text(json.dumps(dict(base,command=['python3',str(w/'strict-stack.py'),str(out)],out=str(w/'runs/c1-stack')),indent=2))
old=Path('/home/dombarker/project-offloads/aspis-r1-rollover-measurement-20261019')
for flow in ['transfer','withdrawal']:
 for pairs in [13,255,1023]:
  label=f'{flow}-{pairs}';cmd=json.loads((old/'runs'/(label+'-measure1')/'command.json').read_text())['argv'][4:]
  cmd[2]=str(w/'candidate1-artifacts/aspis_r1_cost_probe_program.so');cmd[4]=str(w/('candidate1-'+label+'-evidence.json'));cmd[5]=str(w/('candidate1-'+label+'-task'))
  (w/(label+'.json')).write_text(json.dumps(dict(base,command=cmd,out=str(w/'runs'/('c1-'+label)),native_driver_features=['private-leaf-salts']),indent=2))
