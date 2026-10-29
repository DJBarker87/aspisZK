"""Source excerpts for the previously unresolved op IDs; no purity claim."""
from pathlib import Path
import json,lzma,hashlib,subprocess
E=Path('evidence/pv-cx-20261029');O=Path('evidence/pv-cx2-20261029')
x=json.loads(lzma.open(E/'archives/N73309.llbc.xz').read())
files={json.dumps(f['name'],sort_keys=True):f for f in x['translated']['files']}
y=json.loads((E/'effect-interface.json').read_text());out=[]
def excerpt(span):
 key=json.dumps(span['file'],sort_keys=True)
 f=files[key];s=f['contents'];
 if s is None:
  path=f['name']['Local'];prefix='/home/dombarker/project-offloads/codex-pv-cx-20261029/src/'
  if path.startswith(prefix):
   rel=path.removeprefix(prefix);s=subprocess.check_output(['git','show','27b582ca44:'+rel],text=True)
  else:return dict(file=span['file'],status='not embedded',span=span)
 lines=s.splitlines();beg=span['beg']['line'];end=span['end']['line'];return dict(file=span['file'],sha256=hashlib.sha256(s.encode()).hexdigest(),first_line=max(1,beg-2),text='\n'.join(lines[max(0,beg-3):min(len(lines),end+35)]))
for r in y['opaque_functions']:
 if r['effect_class']:continue
 out.append(dict(id=r['llbc_fun_id'],name='::'.join(t['Ident'][0] for t in r['rust_name_structured'] if 'Ident' in t),definition=excerpt(r['definition']),call_sites=[excerpt(s['source']) for s in r['source_call_sites']]))
assert len(out)==62
(O/'unresolved-source-sites.json').write_text(json.dumps(out,indent=2)+'\n')
print('\n\n'.join(str(r['id'])+' '+r['name']+'\n'+r['definition'].get('text','NOT EMBEDDED') for r in out))
