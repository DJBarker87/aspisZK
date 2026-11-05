"""Serial positive/control windows, original harness name; no limit changes."""
from pathlib import Path
import json,hashlib,subprocess,os,difflib
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/'
for limb in range(8):
 src=(E/'NHF_WIDE_WINDOW_TEMPLATE.rs.txt').read_text().replace('NHF_WINDOW_VALUE',str(limb));(E/'NHF_wide.rs.txt').write_text(src)
 pins=json.loads((E/'NHF_SOURCE_PINS.json').read_text());pins[C+'NHF_wide.rs']=hashlib.sha256(src.encode()).hexdigest();(E/'NHF_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
 patch=(E/'NHF_native.patch').read_text();start=patch.index('--- /dev/null\n+++ b/'+C+'NHF_wide.rs\n');patch=patch[:start]+''.join(difflib.unified_diff([],src.splitlines(True),fromfile='/dev/null',tofile='b/'+C+'NHF_wide.rs'));(E/'NHF_native.patch').write_text(patch)
 for bad in [False,True]:
  a=f'NHF_K{15+2*limb+int(bad):03d}';env=dict(os.environ)
  if bad:env['NHF_BAD_VIEW']='1'
  with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NHF_run.py'),a,'kani','verifier::candidate::NHF_wide::wide_view_result'],stdout=f,stderr=subprocess.STDOUT,env=env)
  text=(E/a/'stdout.log').read_text() if (E/a/'stdout.log').exists() else ''
  good=('VERIFICATION:- FAILED' in text and 'Failed Checks: assertion failed' in text) if bad else 'VERIFICATION:- SUCCESSFUL' in text
  row=dict(attempt=a,limb=limb,control=bad,exit=r.returncode,expected_verdict=good)
  with (E/'NHF_WINDOW_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
  print(json.dumps(row),flush=True)
  if not good or 'timed out' in text.lower():raise SystemExit('STOP this projected shape; inspect and split')
