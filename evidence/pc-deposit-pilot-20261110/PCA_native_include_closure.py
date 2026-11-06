from pathlib import Path
import json,lzma,base64,hashlib,re,posixpath,subprocess
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
x=json.loads(lzma.decompress((E/'PCA_NATIVE_FROZEN_INPUTS.json.xz').read_bytes()));updates=json.loads((E/'PCA_NATIVE_REPAIR_FILES.json').read_text());pending=[n for n in x if n.endswith('.rs')];seen=set();added=[]
while pending:
 p=pending.pop()
 if p in seen:continue
 seen.add(p);s=base64.b64decode(x[p]).decode(errors='replace')
 refs=re.findall(r'\bpath\s*=\s*"([^"]+)"',s)+re.findall(r'include!\s*\(\s*"([^"]+\.rs)"',s)
 # Also include this selection's explicit reported missing file.
 if p=='crates/aspis-statement/src/pool_v1/mod.rs':refs+=[]
 for rel in refs:
  if rel.startswith('/'):continue
  n=posixpath.normpath(posixpath.join(posixpath.dirname(p),rel))
  if n.startswith('../') or n in x:continue
  q=subprocess.run(['git','show',rev+':'+n],capture_output=True)
  if q.returncode:continue
  raw=q.stdout
  try:text=raw.decode()
  except UnicodeDecodeError:continue
  x[n]=base64.b64encode(raw).decode();updates['PCA_src/'+n]=text;added.append(dict(path=n,sha256=hashlib.sha256(raw).hexdigest(),from_source=p))
  if n.endswith('.rs'):pending.append(n)
# Reported compiler path is normative if it was generated from a nested module.
required='docs/research/v8-r0-zk-20261009/refine/diffharness/tests/glue_gen.rs'
if required not in x:
 raw=subprocess.check_output(['git','show',rev+':'+required]);x[required]=base64.b64encode(raw).decode();updates['PCA_src/'+required]=raw.decode();added.append(dict(path=required,sha256=hashlib.sha256(raw).hexdigest(),from_source='PCA_K007 exact compiler diagnostic'))
pins={n:hashlib.sha256(base64.b64decode(v)).hexdigest() for n,v in x.items()};(E/'PCA_NATIVE_FROZEN_PINS.json').write_text(json.dumps(pins,indent=1)+'\n');updates['PCA_NATIVE_FROZEN_PINS.json']=(E/'PCA_NATIVE_FROZEN_PINS.json').read_text();(E/'PCA_NATIVE_REPAIR_FILES.json').write_text(json.dumps(updates,indent=1)+'\n');raw=json.dumps(x).encode();(E/'PCA_NATIVE_FROZEN_INPUTS.json.xz').write_bytes(lzma.compress(raw));(E/'PCA_NATIVE_FROZEN_INPUTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n');(E/'PCA_K007_INCLUDE_CLOSURE.json').write_text(json.dumps(dict(files=added,validation='same strict pin/source/lock/graph checks; no reference body changed'),indent=1)+'\n')
p=E/'PCA_native_run.py';s=p.read_text().replace("'PCA_K006','PCA_K007']","'PCA_K006','PCA_K007','PCA_K008','PCA_K009']");p.write_text(s)
print('Frozen include closure completed: '+str(len(added))+' additional source files, each individually hashed.')
