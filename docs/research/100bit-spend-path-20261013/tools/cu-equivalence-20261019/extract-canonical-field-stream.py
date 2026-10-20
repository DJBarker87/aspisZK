#!/usr/bin/env python3
"""Exact Weights.pair field-dot region, exposed as an owned helper result.
Only enclosing-scope parameters, module qualifiers and finish continuation are
factored. Both old/new source regions and inverse substitution are audited.
"""
from pathlib import Path
import argparse,subprocess,json,hashlib
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
tool=Path(__file__).resolve().parent;repo=tool.parents[4];out=tool/'canonical-field-stream-input';base=tool/'cu-canonical-dots-input';sha=lambda b:hashlib.sha256(b).hexdigest()
candidate='e58b87665233febecc1b1a75c506eac1a8b72e00';parent='d11f9b2fcbddf68fd1ffec297f987de0aa95a6c0'
def read(rev,path):return subprocess.check_output(['git','-C',str(repo),'show',rev+':'+path])
def item(raw,anchor):
 a=raw.index(anchor);j=raw.index(b'{',a);k=j+1;d=1
 while d:d+=(raw[k:k+1]==b'{')-(raw[k:k+1]==b'}');k+=1
 return a,k,raw[a:k]
outputs={n:(base/n).read_bytes() for n in ['field.rs','field/wide_exact.rs','old_pairing.rs','new_pairing.rs','Cargo.toml','Cargo.lock']};outputs['lib.rs']=(base/'lib.rs').read_bytes()+b'pub mod weights;\npub mod verifier;\npub mod old_stream;\npub mod new_stream;\n'
vp='crates/aspis-r1-cost-probe/src/verifier.rs';wp='crates/aspis-r1-cost-probe/src/weights.rs';pins=[]
raw=read(candidate,vp);a,b,err=item(raw,b'pub enum Error ')
outputs['verifier.rs']=b'#[derive(Clone,Copy,Debug,PartialEq,Eq)]\n'+err+b'\n';pins.append(dict(name='Error',path=vp,revision=candidate,start_byte=a,end_byte_exclusive=b,file_sha256=sha(raw),fragment_sha256=sha(err)))
raw=read(candidate,wp);a,b,field=item(raw,b'pub fn field(');outputs['weights.rs']=b'use crate::field::WideExact as E;\n'+field+b'\n';pins.append(dict(name='field',path=wp,revision=candidate,start_byte=a,end_byte_exclusive=b,file_sha256=sha(raw),fragment_sha256=sha(field)))
for side,rev in [('old',parent),('new',candidate)]:
 raw=read(rev,wp);a=raw.index(b'                let mut pair=crate::fast_pairing::EbyKDot::new();');b=raw.index(b'                parts[kind]=scale.mul(pair.finish());',a);region=raw[a:b];finish=b'pair.finish()';assert region.count(b'pair.push')==1
 changed=region.replace(b'crate::fast_pairing',b'crate::'+side.encode()+b'_pairing');assert changed.replace(b'crate::'+side.encode()+b'_pairing',b'crate::fast_pairing')==region
 outputs[side+'_stream.rs']=b'use crate::{weights::field,field::{WideExact as E,QM31 as K},verifier::Error};\npub fn field_stream(f:&[u8],scratch:&[K],n:usize)->Result<E,Error> {\n'+changed+b'    Ok('+finish+b')\n}\n'
 outputs['fragments/'+side+'-region.rs']=region;outputs['fragments/'+side+'-caller.rs']=item(raw,b'    pub fn pair(')[2]
 pins.append(dict(name=side+'-Weights.pair-field-dot',path=wp,revision=rev,start_byte=a,end_byte_exclusive=b,file_sha256=sha(raw),fragment_sha256=sha(region),continuation='parts[kind]=scale.mul(pair.finish());',inverse_checked=True))
assert outputs['fragments/old-region.rs']==outputs['fragments/new-region.rs']
meta=dict(candidate=candidate,parent=parent,base_kit_pins_sha256=sha((base/'source-pins.json').read_bytes()),fragments=pins,scope='Complete original constructor+for-loop+finish consumer region. Exact f/scratch/n captured as parameters; only pairing module qualifier changed for paired extraction. Return helper finish at same control point; original scale.mul/store/kind-loop remain an arbitrary unchanged continuation. All decoder/scalar read, map_err, try, iterator and push calls retained.',opaque_paths=['crate::weights::field','crate::old_pairing::_::new','crate::old_pairing::_::push','crate::old_pairing::_::finish','crate::new_pairing::_::new','crate::new_pairing::_::push','crate::new_pairing::_::finish'],roots=['crate::old_stream::field_stream','crate::new_stream::field_stream'],kit_files={n:sha(b) for n,b in outputs.items()})
outputs['source-pins.json']=(json.dumps(meta,indent=2)+'\n').encode()
for name,data in outputs.items():
 p=out/name
 if args.check:assert p.read_bytes()==data,name
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
print(json.dumps(dict(check=args.check,files=len(outputs),old_new_region_identical=True)))
