from pathlib import Path
import json
E=Path(__file__).resolve().parent;C=Path('/private/tmp/pv-kscan-cache-20261028');R='/home/dombarker/project-offloads/codex-pv-kscan-20261028';W=R+'/d347/workspace';db=json.loads((C/'d347-source-db.json').read_text());ps=json.loads((E/'d347-input.json').read_text())['passes'];rs=json.loads((C/'d347-receipts.json').read_text());plans=json.loads((E/'d347-plans.json').read_text());payload={};bs=json.loads((E/'d347-source-bindings.json').read_text())
plans['D025']=dict(plans['D017'],replacement_for='D017',change='Restore original hash-pinned sibling pv-rw19 proof inputs required by rw21; previous scope mixed retained sibling version and failed type-check, no solver.')
for name in ['D018','D019','D020','D021','D022','D023','D025']:
 p=next(p for p in ps if p['index']==plans[name]['indices'][0]);m=rs[p['receipt_blob']]['source_sha256'];m={k:h for k,h in m.items() if k.endswith(('.rs','Cargo.toml','Cargo.lock')) and not k.startswith('/')};miss={k:h for k,h in m.items() if h not in db};assert not miss,(name,miss)
 updates={W+'/'+k:db[h]['text'] for k,h in m.items()};upath=R+'/d347/'+name+'/updates.json';payload[upath]=json.dumps(updates);plans[name]['updates_file']=upath;plans[name]['source_checks']={W+'/'+k:h for k,h in m.items()}
 bs=[b for b in bs if b['run']!=name];bs.append(dict(run=name,indices=plans[name]['indices'],basis='Complete original receipt Rust/manifest/lock source map, including sibling proof-module dependencies',files=[dict(path=W+'/'+k,sha256=h,origin=db[h]['origin'],kind=db[h]['kind']) for k,h in m.items()]))
(E/'d347-plans.json').write_text(json.dumps(plans,indent=2)+'\n');(E/'d347-source-bindings.json').write_text(json.dumps(bs,indent=2)+'\n');(C/'d347-repair-payload.json').write_text(json.dumps(payload))
