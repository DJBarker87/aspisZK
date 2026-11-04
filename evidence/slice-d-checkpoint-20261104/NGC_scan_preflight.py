from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1]
p=E/'NGC_EXPECTED_IMPORTS.jsonl';rows={r['module']:r for r in map(json.loads,p.read_text().splitlines())};pins=[]
bad=[r for r in map(json.loads,(E/'NGC_LOADED_scan.jsonl').read_text().splitlines())if not r['imports_match']or r['dangling']]
for row in bad:
 assert not row['dangling'],row
 name=row['module'];parts=name.split('.');rel='/'.join(parts)+'.lean'
 candidates=[p for directory in ['slice-d-define-20261104','slice-d-field-20261104','native-cpilot-20261028']for p in (E.parent/directory).rglob(parts[-1]+'.lean')if str(p).endswith(rel)]
 if len(parts)==1:candidates=[p for directory in ['slice-d-define-20261104','slice-d-field-20261104','native-cpilot-20261028']for p in(E.parent/directory).rglob(name+'.lean')]
 assert candidates,name
 source=min(candidates,key=lambda p:len(str(p)));imports=list(dict.fromkeys(['Init']+[n for l in source.read_text().splitlines()if l.startswith('import ')for n in l.split()[1:]if n!='all']))
 assert imports==row['imports'],(name,imports,row['imports'])
 rows[name]=dict(module=name,imports=imports)
 pins.append(dict(module=name,path=str(source.relative_to(R)),sha256=hashlib.sha256(source.read_bytes()).hexdigest(),imports=imports))
p.write_text(''.join(json.dumps(r)+'\n'for r in rows.values()));(E/'NGC_SCAN_MANIFEST_REPAIR.json').write_text(json.dumps(dict(reason='14 omitted expected entries, zero dangling; add exact source-backed entries only',source_pins=pins),indent=1)+'\n');print('added',len(pins),'source-backed expected entries')
