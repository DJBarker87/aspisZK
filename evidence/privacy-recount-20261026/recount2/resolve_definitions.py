from pathlib import Path
import json,subprocess,hashlib
P=Path(__file__).resolve().parent;rows=json.loads((P.parent/'rows.json').read_text());pins=json.loads((P/'pins.json').read_text());m=json.loads((P/'manifest.json').read_text());cache={};audit=[]
for r in rows:
 path=r.get('definition','').split('#')[0]
 if not path:continue
 if path not in cache:
  entry=None
  for label in ['research','rw','dict','runjoin','srcid','l3','rebase','cb']:
   rev=pins[label]['revision'];p=subprocess.run(['git','show',rev+':'+path],capture_output=True)
   if p.returncode:continue
   dest=P/label/(path+'.txt' if path.endswith('.lean') else path);dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.stdout)
   entry=dict(label=label,revision=rev,path=path,local=str(dest),sha256=hashlib.sha256(p.stdout).hexdigest());break
  cache[path]=entry
  if entry and not any(e['local']==entry['local'] for e in m):m.append(entry)
 audit.append(dict(id=r['id'],original_definition=r['definition'],resolved=cache[path]))
(P/'resolved-definitions.json').write_text(json.dumps(audit,indent=2)+'\n');(P/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
print('Missing',[(e['id'],e['original_definition']) for e in audit if not e['resolved']]);print('Captured',len(cache),'unique original defining paths')
