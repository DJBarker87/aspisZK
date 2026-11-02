from pathlib import Path
import json,lzma,base64,subprocess,re,hashlib
E=Path(__file__).resolve().parent;report=[]
for name,rev,root in [('B3-source','daa87066400b0b8e72117f0d9f8bbefb8f2ecc2e','b3-source'),('B3-rest-source','daa87066400b0b8e72117f0d9f8bbefb8f2ecc2e','b3-rest-source'),('Arity-source','f3071faf749b28cf563e25984728489a29d52c79','arity-source')]:
 p=E/(name+'.json.xz');files={n:base64.b64decode(b)for n,b in json.loads(lzma.decompress(p.read_bytes())).items()};extra={}
 paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'docs/research/v8-r0-zk-20261009/refine/writers','docs/research/v8-r0-zk-20261009/refine/blockwriters','docs/research/v8-r0-zk-20261009/refine/poseidon','docs/research/v8-r0-zk-20261009/refine/diffharness/tests/glue_gen.rs'],text=True).splitlines()
 for n in paths:
  if n in files:continue
  b=subprocess.check_output(['git','show',rev+':'+n]);files[n]=b;extra[n]=b
 t=files['Cargo.toml'].decode();members=['crates/aspis-core','crates/aspis-statement']+(['crates/aspis-prover']if name.startswith('B3')else[])+['docs/research/v8-r0-zk-20261009/refine/'+n for n in ['writers','blockwriters','poseidon']]
 t=re.sub(r'members\s*=\s*\[.*?\]','members='+json.dumps(members),t,count=1,flags=re.S);files['Cargo.toml']=t.encode();extra['Cargo.toml']=t.encode()
 raw=json.dumps({n:base64.b64encode(b).decode()for n,b in files.items()}).encode();p.write_bytes(lzma.compress(raw,preset=6));(E/(name+'.json.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n')
 if name=='B3-source':
  raw=json.dumps({n:base64.b64encode(b).decode()for n,b in extra.items()}).encode();(E/'B3-closure-addendum.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'B3-closure-addendum.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
 report.append({'payload':name,'revision':rev,'root':root,'extra_files':[{'path':n,'sha256':hashlib.sha256(b).hexdigest()}for n,b in extra.items()],'reason':'Source-only dependency preflight found unconditional aspis-statement host writer dependencies; recover the exact frozen directories and generated literal include before the first compiler launch. No selected harness/body changed.'})
(E/'PACKAGE-CLOSURE-ADDENDUM.json').write_text(json.dumps(report,indent=2)+'\n')
print([(r['payload'],len(r['extra_files']))for r in report])
