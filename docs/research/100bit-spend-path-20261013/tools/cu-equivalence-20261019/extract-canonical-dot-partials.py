#!/usr/bin/env python3
"""Inverse-audited fission of the exact nested shared-point partial loop."""
from pathlib import Path
import argparse,json,hashlib,re
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
tool=Path(__file__).resolve().parent;base=tool/'canonical-dot-clients-input';out=tool/'canonical-dot-partials-input';sha=lambda b:hashlib.sha256(b).hexdigest()
files={p.relative_to(base).as_posix():p.read_bytes()for p in base.rglob('*')if p.is_file()and p.name!='source-pins.json'}
pins=json.loads((base/'source-pins.json').read_text()); fissions=[]
for side in ['old','new']:
 raw=files[side+'_clients.rs'];start=raw.index(b' let mut dot=') if b' let mut dot='in raw else raw.index(b'let mut dot=')
 # Select the complete inner constructor/loop/finish assignment only.
 start=raw.index(b'                let mut dot=');end=raw.index(b'                partials[s]=dot.finish();',start)+len(b'                partials[s]=dot.finish();')
 region=raw[start:end];finish=b'                partials[s]=dot.finish();';assert region.endswith(finish)
 body=region[:-len(finish)]+b'    Ok(dot.finish())\n'
 call=b'                partials[s]=shared_row(f,common,s)?;'
 changed=raw[:start]+call+raw[end:]
 # Syntactic expansion and Rust Result bind associativity restore the exact source.
 assert changed[:start]+region+changed[start+len(call):]==raw
 changed+=b'\npub fn shared_row(f:&[u8],common:&[K;16],s:usize)->Result<E,Error> {\n'+body+b'}\n'
 files[side+'_clients.rs']=changed
 fissions.append(dict(side=side,original_region_sha256=sha(region),helper_body_sha256=sha(body),expanded_original_identical=True,rule='Constructor+inner loop+finish lifted as Result-valued helper. The sole added ? propagates the exact pre-existing inner-loop Error; no computation can fail between helper success and the same partials[s] write.'))
meta=dict(base_pins_sha256=sha((base/'source-pins.json').read_bytes()),fissions=fissions,roots=['crate::'+s+'_clients::'+f for s in ['old','new']for f in ['shared_partials','shared_row']],opaque_paths=pins['opaque_paths'],kit_files={n:sha(b)for n,b in files.items()})
files['source-pins.json']=(json.dumps(meta,indent=2)+'\n').encode()
for n,b in files.items():
 p=out/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps(dict(check=a.check,fissions=len(fissions),inverse_source_audit=True)))
