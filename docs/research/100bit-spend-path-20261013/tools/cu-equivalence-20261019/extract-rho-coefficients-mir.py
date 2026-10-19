#!/usr/bin/env python3
"""Reproduce the bounded optimized-MIR experiment's extraction-only input."""
from pathlib import Path
import argparse,hashlib,json,re
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest();original=here/'rho-coefficients-input'
raw=(original/'lib.rs').read_bytes();pattern=rb'((?:pub(?:\([^)]*\))?\s+)?fn [^{}]+\{unreachable!\(\)\})'
lib,count=re.subn(pattern,rb'#[inline(never)]\n\1',raw);assert count>0
for side in ['old','new']:
 helper=(original/f'fragments/{side}-helper.rs').read_bytes();assert helper in raw and helper in lib
pins=dict(original_source_pins_sha256=sha((original/'source-pins.json').read_bytes()),original_lib_sha256=sha(raw),lib_sha256=sha(lib),opaque_stub_noinline_attributes=count,selected_source_helper_bodies_unchanged=True,scope='One targeted optimized-MIR extraction with pinned compiler/producer. Only unreachable external stub declarations gain noinline so compiler inlining cannot substitute their fake bodies into the actual source loop. No production Rust or compiler changes.')
outputs={'lib.rs':lib,'source-pins.json':(json.dumps(pins,indent=2)+'\n').encode()}
for name in ['Cargo.toml','Cargo.lock']:outputs[name]=(original/name).read_bytes()
for n,b in outputs.items():
 p=here/'rho-coefficients-mir-input'/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(exist_ok=True);p.write_bytes(b)
print(json.dumps(dict(check=a.check,selected_source_helper_bodies_unchanged=True)))
