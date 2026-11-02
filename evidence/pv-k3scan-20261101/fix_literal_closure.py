from pathlib import Path
import json,lzma,base64,subprocess,re,posixpath,hashlib
E=Path(__file__).resolve().parent;reports=[]
for name,rev in [('B3-source','daa87066400b0b8e72117f0d9f8bbefb8f2ecc2e'),('B3-rest-source','daa87066400b0b8e72117f0d9f8bbefb8f2ecc2e'),('Arity-source','f3071faf749b28cf563e25984728489a29d52c79')]:
 p=E/(name+'.json.xz');files={n:base64.b64decode(b)for n,b in json.loads(lzma.decompress(p.read_bytes())).items()};extras={};checked=[];unresolved=[]
 for round in range(12):
  missing=set()
  for n,b in list(files.items()):
   if not n.endswith('.rs'):continue
   t=b.decode(errors='replace')
   for pat in [r'#\s*\[\s*path\s*=\s*"([^"]+)"',r'\binclude(?:_str|_bytes)?!\(\s*"([^"]+)"']:
    for m in re.finditer(pat,t):
     q=posixpath.normpath(posixpath.join(posixpath.dirname(n),m[1]));checked.append((n,m[1],q))
     if q not in files and not q.startswith('../'):missing.add(q)
  found=0
  for q in sorted(missing):
   r=subprocess.run(['git','show',rev+':'+q],capture_output=True)
   if r.returncode:continue
   files[q]=r.stdout;extras[q]=r.stdout;found+=1
   # Include the module's complete sibling source directory for plain mod declarations.
   if q.startswith('tools/') and q.endswith('.rs') and posixpath.dirname(q)!='tools':
    parent=posixpath.dirname(q)
    paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,parent],text=True).splitlines()
    for x in paths:
     if x not in files and x.endswith(('.rs','.toml','.json','.txt')):
      b=subprocess.check_output(['git','show',rev+':'+x]);files[x]=b;extras[x]=b
  if not found:break
 assert round<11,'module include fixpoint not reached'
 # Retain missing cfg(test) fixture paths explicitly; they are not lib/Kani inputs.
 unresolved=sorted(q for q in missing if q not in files)
 raw=json.dumps({n:base64.b64encode(b).decode()for n,b in files.items()}).encode();p.write_bytes(lzma.compress(raw,preset=6));(E/(name+'.json.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n')
 raw=json.dumps({n:base64.b64encode(b).decode()for n,b in extras.items()}).encode();(E/(name+'-literal-addendum.json.xz')).write_bytes(lzma.compress(raw,preset=6));(E/(name+'-literal-addendum.json.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n')
 reports.append({'payload':name,'revision':rev,'additions':[{'path':n,'sha256':hashlib.sha256(b).hexdigest()}for n,b in extras.items()],'literal_paths_checked':len(set(checked)),'unresolved_literal_paths':unresolved})
(E/'LITERAL-CLOSURE-REPAIR.json').write_text(json.dumps({'failed_id':'K79208','failure':'compiler could not read tools/r1-builder-reference/tree.rs; no verification result','charged_invocations':1,'replacement_id':'K79209','change':'Restore exact immutable module/literal include closure, not a theorem/assertion/bound change','packages':reports},indent=2)+'\n');print([(r['payload'],len(r['additions']),len(r['unresolved_literal_paths']))for r in reports])
