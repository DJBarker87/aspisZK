#!/usr/bin/env python3
"""Independent exact host Wide embedding primitive; no Backend/build claim."""
from pathlib import Path
import argparse,hashlib,json
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--check',action='store_true');a=ap.parse_args()
 base=H/'input';bp=json.loads((base/'source-pins.json').read_text());extra=json.loads((H/'input-build/source-pins.json').read_text());c0=[x for x in extra['cuts'] if x['name']=='wide_c0'];assert len(c0)==1
 c0bytes=(H/'input-build/fragments/wide_c0.rs').read_bytes();assert sha(c0bytes)==c0[0]['sha256']
 s=(base/'lib.rs').read_text();assert sha(s.encode())==bp['kit_files']['lib.rs'];assert s.count('impl WideExact {\n')==1
 s=s.replace('impl WideExact {\n','impl WideExact {\n'+c0bytes.decode()+'\n',1)
 s+='\npub fn embed_project_entry(value:field::QM31)->field::QM31 {field::WideExact::from_qm31(value).c0()}\n'
 outputs={'lib.rs':s.encode(),'Cargo.toml':(base/'Cargo.toml').read_bytes(),'Cargo.lock':(base/'Cargo.lock').read_bytes(),'fragments/wide_c0.rs':c0bytes}
 bp.update(cuts=bp['cuts']+c0,kit_files={n:sha(b) for n,b in outputs.items()},root_target='crate::embed_project_entry',namespace='AspisC2HostEmbedding',classification='Exact host WideExact::from_qm31, canonical_qm31, c0 primitive; no Backend/constructor ownership claim',boundaries={'scope':'Only actual host field embedding/projection primitive. No constructors/encoding/hash/salts/root/custody operations reachable.'})
 outputs['source-pins.json']=(json.dumps(bp,indent=2,sort_keys=True)+'\n').encode()
 for n,b in outputs.items():
  p=a.out/n
  if a.check:assert p.read_bytes()==b,n
  else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 print(json.dumps({'check':a.check,'lib_sha256':sha(s.encode()),'pins_sha256':sha(outputs['source-pins.json'])}))
if __name__=='__main__':main()
