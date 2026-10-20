#!/usr/bin/env python3
from pathlib import Path
import argparse,hashlib,json,subprocess,importlib.util,re
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();tool=Path(__file__).resolve().parent;area=tool.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();seed=tool/'canonical-field-stream-input'
spec=importlib.util.spec_from_file_location('cut',area/'tools/public-serializer-extraction-kit/extract.py');cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
class Source:
 def __init__(self,raw):self.raw=raw
 def read_bytes(self):return self.raw
pins=[];previous=None
for rev in ['f458169f705f25b04e1e29546c621e4665e0f64c','39c2971dd16c95858a4cfd2c9ae35da052eacfa9']:
 raw=subprocess.check_output(['git','show',rev+':crates/aspis-r1-cost-probe/src/weights.rs']);item,start,end,first,last=cut.find_item(Source(raw),'    pub fn new(variant:Variant,alpha:&[K;10],z:&[SecureCirclePoint;2])')
 if previous is not None:assert item==previous
 previous=item;assert item.count(b'.extra)')==1;assert item.count(b'alpha[8]')==1 and item.count(b'alpha[9]')==1
 assert b'core::ptr::addr_of_mut!((*p).extra).write([alpha[8],alpha[9]]);'in item
 pins.append(dict(revision=rev,constructor_sha256=sha(item),start_byte=start,end_byte_exclusive=end))
outputs={name:(seed/name).read_bytes()for name in ['Cargo.toml','Cargo.lock','field.rs','field/wide_exact.rs']}
outputs['lib.rs']=b'#![allow(dead_code,unused_imports)]\npub mod field;\npub fn extra(alpha:&[field::QM31;10])->[field::QM31;2]{[alpha[8],alpha[9]]}\n'
meta=dict(original_constructor_pins=pins,projection_expression='[alpha[8],alpha[9]]',field_write_count=1,subsequent_extra_writes_or_field_reads=0,source_projection_boundary='Unchanged owning constructor has one direct extra write from immutable semantic-alpha array, no extra mutations/field aliases in remaining constructor. Standard source ownership/field-write frame semantics binds later immutable self.extra reads to this value. All allocation, points and factor computation stays in unchanged source context; this focused extraction proves only the exact projected expression, not the unsafe constructor or allocator anew.',roots=['crate::extra'],opaque_paths=[],kit_files={n:sha(b)for n,b in outputs.items()})
outputs['source-pins.json']=(json.dumps(meta,indent=2)+'\n').encode()
for name,data in outputs.items():
 p=tool/'retained-weights-extra-input'/name
 if a.check:assert p.read_bytes()==data,name
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
print(json.dumps(dict(check=a.check,constructor_unchanged=True,single_extra_write=True)))
