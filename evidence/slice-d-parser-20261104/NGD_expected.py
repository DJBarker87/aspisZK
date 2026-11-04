from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
rows=[json.loads(l)for l in (E/'NGD_EXPECTED_IMPORTS.jsonl').read_text().splitlines()];tables={r['module']:r['imports']for r in rows}
for m in list(tables):
 if m.startswith('NGD_') and 'Init'not in tables[m]:tables[m].insert(0,'Init')
files=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],text=True).splitlines();prefix='docs/research/100bit-spend-path-20261013/lean/'
pins=[];todo=['NBE_SlotLoop','NCO_LoopSteps']
while todo:
 m=todo.pop()
 if m in tables:continue
 rel=m.replace('.','/')+'.lean';candidates=[n for n in files if n==prefix+rel]
 if not candidates:candidates=[n for n in files if n.endswith('/'+rel)and '/sources/'not in n]
 assert candidates,('missing source baseline',m)
 path=candidates[0];raw=subprocess.check_output(['git','show','HEAD:'+path]);im=['Init']+list(dict.fromkeys(n for l in raw.decode().splitlines()if l.startswith('import ')for n in l[7:].split()if n!='all'))
 tables[m]=list(dict.fromkeys(im));todo.extend(im)
 p=E/'NGD_pinned_baselines'/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
 pins.append(dict(module=m,path=path,sha256=hashlib.sha256(raw).hexdigest(),imports=tables[m]))
(E/'NGD_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=im))+'\n'for m,im in sorted(tables.items())))
(E/'NGD_BASELINE_ADDITIONS.json').write_text(json.dumps(pins,indent=2)+'\n')
