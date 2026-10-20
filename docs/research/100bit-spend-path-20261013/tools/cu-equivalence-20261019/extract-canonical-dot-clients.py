#!/usr/bin/env python3
"""Pin exact shared-point partial/high loops and final enumerate dot client."""
from pathlib import Path
import argparse,hashlib,json,subprocess,re
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
tool=Path(__file__).resolve().parent;repo=tool.parents[4];base=tool/'canonical-field-stream-input';out=tool/'canonical-dot-clients-input';sha=lambda b:hashlib.sha256(b).hexdigest()
candidate='e58b87665233febecc1b1a75c506eac1a8b72e00';parent='d11f9b2fcbddf68fd1ffec297f987de0aa95a6c0'
def read(rev,path):return subprocess.check_output(['git','-C',str(repo),'show',rev+':'+path])
outputs={name:(base/name).read_bytes() for name in ['field.rs','field/wide_exact.rs','old_pairing.rs','new_pairing.rs','Cargo.toml','Cargo.lock','weights.rs','verifier.rs']};outputs['lib.rs']=(base/'lib.rs').read_bytes().split(b'pub mod old_stream;')[0]+b'pub mod old_clients;\npub mod new_clients;\n';pins=[]
for side,rev in [('old',parent),('new',candidate)]:
 path='crates/aspis-r1-cost-probe/src/weights.rs';raw=read(rev,path)
 a=raw.index(b'            let mut partials=[E::ZERO;4];');b=raw.index(b'            for (kind,k) in [(1usize,0usize),(3usize,2usize)]',a);partials=raw[a:b]
 c=raw.index(b'                let mut high=crate::fast_pairing::EbyKDot::new();',b);d=raw.index(b'                let scale=Self::scalar_factor(',c);high=raw[c:d]
 vp='crates/aspis-r1-cost-probe/src/verifier.rs';vr=read(rev,vp);e=vr.index(b'    let mut dot=crate::fast_pairing::EbyKDot::new();',vr.index(b'pub fn finish_relation('));f=vr.index(b'    let actual=dot.finish();',e);final=vr[e:f]
 def region(name,path,source,a,b,data,replacements):
  pins.append(dict(name=side+'-'+name,path=path,revision=rev,start_byte=a,end_byte_exclusive=b,file_sha256=sha(source),fragment_sha256=sha(data),substitutions=[{'old':x.decode(),'new':y.decode()}for x,y in replacements],inverse_checked=True))
  transformed=data
  for old,new in replacements:assert transformed.count(old)>0;transformed=transformed.replace(old,new)
  inverse=transformed
  for old,new in reversed(replacements):
   inverse=re.sub(rb"(?<![A-Za-z0-9_])"+re.escape(new)+rb"(?![A-Za-z0-9_])",lambda _:old,inverse) if new in [b"f",b"weights"] else inverse.replace(new,old)
  assert inverse==data
  outputs['fragments/'+side+'-'+name+'.rs']=data
  return transformed
 prefix=b'use crate::{weights::field,field::{WideExact as E,QM31 as K},verifier::Error};\n'
 common=[(b'crate::fast_pairing',b'crate::'+side.encode()+b'_pairing')]
 pp=region('partials',path,raw,a,b,partials,common)
 hh=region('high',path,raw,c,d,high,common+[(b'self.factors[k][4][s]',b'scalars[s]')])
 ff=region('final',vp,vr,e,f,final,common+[(b'a.weights',b'weights'),(b'v.final_message',b'f')])
 outputs[side+'_clients.rs']=prefix+b'pub fn shared_partials(f:&[u8],common:&[K;16])->Result<[E;4],Error> {\n'+pp+b'    Ok(partials)\n}\n'+b'pub fn shared_high(partials:&[E;4],scalars:&[K;4])->Result<E,Error> {\n'+hh+b'    Ok(high.finish())\n}\n'+b'pub fn final_stream(f:&[u8],weights:&[K])->Result<E,Error> {\n'+ff+b'    Ok(dot.finish())\n}\n'
for region in ['partials','high','final']:assert outputs['fragments/old-'+region+'.rs']==outputs['fragments/new-'+region+'.rs']
meta=dict(candidate=candidate,parent=parent,base_source_pins_sha256=sha((base/'source-pins.json').read_bytes()),fragments=pins,scope='Exact original complete constructor/loop/finish regions. Enclosing lexical inputs captured as parameters with listed inverse substitutions; original error map/try/iterators retained. Unchanged surrounding body remains compositional computational context.',opaque_paths=['crate::weights::field','crate::old_pairing::_::new','crate::old_pairing::_::push','crate::old_pairing::_::finish','crate::new_pairing::_::new','crate::new_pairing::_::push','crate::new_pairing::_::finish'],roots=['crate::'+side+'_clients::'+fn for side in ['old','new'] for fn in ['shared_partials','shared_high','final_stream']],kit_files={n:sha(b)for n,b in outputs.items()})
outputs['source-pins.json']=(json.dumps(meta,indent=2)+'\n').encode()
for name,data in outputs.items():
 p=out/name
 if args.check:assert p.read_bytes()==data,name
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
print(json.dumps(dict(check=args.check,files=len(outputs),regions=3,old_new_regions_identical=True)))
