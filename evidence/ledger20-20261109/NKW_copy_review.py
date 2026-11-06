from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=E/'NKW_NATIVE_REVIEW.json';x=json.loads(p.read_text());K='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
kmx={'KMX_stubs.rs':'ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138','KMX_native.rs':'cf719c47b5c8c91dcc369984c01bd0b8531b25210e344c9fd06db21b30171880','KMX_CopyMeaning.lean':'2baec49a3446a3bbb2be6f992c97d0a6897534a1cd308db8746194dedf665f2b'}
for c in x['checks']:
 if c['provider']in ['NKI','NKL']:
  assert K in c['source_hashes'].values();c['copy_fidelity']='Exact KMX patch hash in receipt; matching inverse control under same configuration'
 elif c['provider']=='NKM':
  s=json.loads((E.parent/'circle-points-20261108'/c['attempt']/'sources/NKM_SOURCE_PINS.json').read_text());assert all(s[k]==v for k,v in kmx.items());c['copy_fidelity']='Exact official KMX helper hashes enforced by receipt-pinned NKM_gate.py; matched copy controls K011/K003,K029/K030'
 else:c['copy_fidelity']='No new row credit; actual returned-value/error support only. Allocation identity/effects OPEN.'
p.write_text(json.dumps(x,indent=1)+'\n');print('KMX configuration checks PASS for all native receipts supporting proposed admissions')
