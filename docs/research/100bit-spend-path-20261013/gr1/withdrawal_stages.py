#!/usr/bin/env python3
"""Fill the missing withdrawal diagnostics using retained stage ELFs/drivers."""
import pathlib,subprocess,shutil
r=pathlib.Path('/home/dombarker/project-offloads/aspis-100bit-path-20261013');b=r/'results/100bit-path-20261013';p2=pathlib.Path('/home/dombarker/project-offloads/aspis-r1-p2-20261010')
for stage in ['pairing','terminal','rho-clean','geometry-dots','d18']:
 out=r/f'results/gr1-cost-20261013/withdrawal-stages/{stage}/S2';f=out/'fixtures';f.mkdir(parents=True,exist_ok=False)
 for suffix in ['proof.bin','public.bin','fixture.json']:
  shutil.copyfile(p2/f'results/r1-precheck-20261010/S2/fixtures/withdrawal.{suffix}',f/f'withdrawal.{suffix}')
 driver=p2/('results/r1-precheck-20261010/bin/r1-cu-driver' if stage in ['pairing','terminal'] else 'target/release/aspis-r1-cu-probe')
 subprocess.run(['python3','/tmp/gr1-run.py','withdrawal-stage-'+stage,str(r),str(driver),'diagnostic',str(b/stage/'bin/aspis_r1_cost_probe_program.so'),str(out),'withdrawal','10'],check=True,stdout=subprocess.DEVNULL)
