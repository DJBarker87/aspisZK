"""Retain raw emissions, route own imports, and append an axiom audit.
No extractor/backend guard or generated resource option is changed.
"""
from pathlib import Path
import re,sys,hashlib,json
D=Path(__file__).resolve().parent;key=sys.argv[1];op=key.split('-')[0];L=D/'lean';L.mkdir(exist_ok=True);adapters=[]
for phase in ['Types','Funs']:
 raw=D/f'generated-{key}'/(phase+'.lean');s=raw.read_text();namespace=re.search(r'^namespace (\S+)',s,re.M)[1];module=namespace+'_'+phase
 if phase=='Funs':s=re.sub(r'^import \S+\.Types$',f'import {namespace}_Types',s,flags=re.M)
 names=re.findall(r'^(?:def|structure|inductive|class|abbrev) ([\w.]+)',s,re.M)
 s=s.replace('end '+namespace,'\n'.join('#print axioms '+n for n in names)+'\nend '+namespace)
 (L/(module+'.lean')).write_text(s);adapters.append(dict(module=module,raw_sha256=hashlib.sha256(raw.read_bytes()).hexdigest(),ported_sha256=hashlib.sha256(s.encode()).hexdigest(),changes='own import routing and #print axioms only',declarations=names))
(D/f'adapters-{key}.json').write_text(json.dumps(adapters,indent=2)+'\n')
