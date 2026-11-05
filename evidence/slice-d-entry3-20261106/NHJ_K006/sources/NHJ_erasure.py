"""Byte-exact cfg erasure validator; no launch or shared infrastructure changes."""
from pathlib import Path
import json,hashlib,re
P='programs/r1-cost-probe/src/'
def erase(n,s,zero):
 annotations=Path(__file__).with_name("NGL_CONTRACT_ANNOTATIONS.json")
 if annotations.exists():
  for attr in json.loads(annotations.read_text()).values():
   if attr in s:s=s.replace(attr,"",1)
 if n==P+'lib.rs':
  prefix='#![cfg_attr(kani,feature(allocator_api))]\n'
  if s.startswith(prefix):s=s[len(prefix):]
 # Only our exact, known sidecar declarations are erased.
 for module in ['NHJ_owned','NHD_meta_calibration','NHD_prefix','NHD_ids','NHD_distinct','NHD_snapshot','NHD_error','NHD_calibration','NHD_owned','NGL_entry','NGL_adapter','NGL_owned']:
  suffix='\n#[cfg(kani)]\n#[path="'+module+'.rs"]\nmod '+module+';\n'
  if s.endswith(suffix):s=s[:-len(suffix)]
 if n==P+'r1_pool_adapter_owned.rs' and zero['instrumented_body'] in s:
  assert s.count(zero['instrumented_body'])==1
  s=s.replace(zero['instrumented_body'],zero['frozen_body'])
 return s

def validate(root,pins,zero):
 rows=[]
 for n,expected in pins.items():
  p=root/n
  if n.endswith('.rs'):
   data=erase(n,p.read_text(),zero).encode()
  else:data=p.read_bytes()
  actual=hashlib.sha256(data).hexdigest();rows.append(dict(path=n,sha256=actual,expected=expected,equal=actual==expected))
 return dict(passed=all(r['equal'] for r in rows),files=len(rows),changed=[r for r in rows if not r['equal']],rows=rows)
