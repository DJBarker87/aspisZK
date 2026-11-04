from pathlib import Path
import subprocess,json,lzma,base64,hashlib,collections
E=Path(__file__).resolve().parent;REL=str(E.relative_to(E.parents[1]));sha=lambda b:hashlib.sha256(b).hexdigest()
needs={h for p in (E/'host').glob('K919*/source-sha256.json') for h in json.loads(p.read_text()).values()}
found={};extra={}
def add(b,origin):
 h=sha(b)
 if h in needs and h not in found:found[h]=origin
for p in E.rglob('*'):
 if p.is_file() and 'host' not in p.parts and '__pycache__' not in p.parts:add(p.read_bytes(),{'file':str(p.relative_to(E))})
revs=subprocess.check_output(['git','log','--format=%H',json.loads((E/'PINS.json').read_text())['entry']+'..HEAD','--',REL],text=True).splitlines()
seen=set()
for r in revs:
 for line in subprocess.check_output(['git','ls-tree','-r',r,'--',REL+'/caller',REL+'/source.json.xz',REL+'/default-source.json.xz'],text=True).splitlines():
  desc,p=line.split('\t',1);blob=desc.split()[2]
  if blob in seen:continue
  seen.add(blob);b=subprocess.check_output(['git','cat-file','blob',blob]);add(b,{'revision':r,'path':p,'git_blob':blob})
  if p.endswith('source.json.xz'):
   for n,v in json.loads(lzma.decompress(b)).items():add(base64.b64decode(v),{'revision':r,'payload':p,'member':n})
# Uncommitted intermediate root before the default module append: recover only
# if its hash equals a recorded input. Never substitute a same-name current body.
b=subprocess.check_output(['git','show','182e38f0a8:'+REL+'/caller/lib.rs'])
for b in [b.replace(b'\n#[path="default.rs"] mod generic_default_gate;\n',b''),b.replace(b'\n#[path="default.rs"] mod generic_default_gate;\n',b'').replace(b'include!("array.rs");',b'#[path="array.rs"] mod array;')]:
 if sha(b) in needs and sha(b) not in found:
  extra[sha(b)]=base64.b64encode(b).decode();add(b,{'recovered_payload':'intermediate-inputs.json.xz','member':sha(b),'recovery':'remove the not-yet-uploaded default-module append; exact receipt SHA required'})
if extra:
 raw=json.dumps(extra).encode();(E/'intermediate-inputs.json.xz').write_bytes(lzma.compress(raw));(E/'intermediate-inputs.json.sha256').write_text(sha(raw)+'\n')
missing=sorted(needs-found.keys());result={'input_hashes':len(needs),'resolved':len(found),'missing':missing,'sources':found}
(E/'SOURCE-INDEX.json').write_text(json.dumps(result,indent=2)+'\n');print('source hashes',len(needs),'resolved',len(found),'missing',missing)
