#!/usr/bin/env python3
import pathlib,subprocess,time,sys
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
for retry in range(10):
 name='srcid8-prefix01-try'+str(retry)
 if (e/('reservation-'+name+'.json')).exists():continue
 with (e/(name+'-client.log')).open('w') as f:
  r=subprocess.run([sys.executable,str(root/'tools/pv-srcid3/resume8-kani.py'),name,'pool_v1::pair_forest_copy_builder::records_proofs::empty_roots::pv_srcid8_helper_prefix01','180'],stdout=f,stderr=subprocess.STDOUT)
 print(name,r.returncode,flush=True)
 if r.returncode!=78:sys.exit(r.returncode)
 for _ in range(3):print('reservation wait 60 seconds',flush=True);time.sleep(60)
sys.exit(78)
