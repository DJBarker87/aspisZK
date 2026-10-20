from pathlib import Path
import hashlib,json,re
H=Path('/home/dombarker/project-offloads/codex-cx-repin-s8-20261020')
F=Path('/home/dombarker/project-offloads/codex-cx-pin-20261020')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for label,path in [('current',H/'extraction-s8-stage2-01/Stage2.llbc'),('inherited',F/'extraction-freeze/Stage2.llbc')]:
 j=json.loads(path.read_text());out=dict(path=str(path),sha256=sha(path),bytes=path.stat().st_size,has_errors=j['has_errors'],charon_version=j['charon_version'])
 (H/(label+'-llbc-pin.json')).write_text(json.dumps(out,indent=2)+'\n')
 if label=='current':
  rows=[]
  for f in j['translated']['fun_decls']:
   if not f:continue
   m=f['item_meta'];name=json.dumps(m['name'])
   if 'aspis_r1_cost_probe' not in name:continue
   if not any(x in name for x in ['verifier','compact']):continue
   rows.append(dict(id=f['def_id'],name=m['name'],span=m['span'],opacity=m['opacity'],source_text=m['source_text'],has_body=f.get('body') is not None,declaration_sha256=hashlib.sha256(json.dumps(f,sort_keys=True,separators=(',',':')).encode()).hexdigest()))
  (H/'llbc-declarations.json').write_text(json.dumps(rows,indent=2)+'\n')
logs=[]
for p in (H/'receipts').rglob('*.log'):
 logs.append(dict(host_path=str(p),sha256=sha(p),bytes=p.stat().st_size))
(H/'log-pins.json').write_text(json.dumps(logs,indent=2)+'\n')
p=H/'receipts/extract-s8-stage2-01-aeneas/stdout.log';lines=p.read_text().splitlines();idx=max(i for i,s in enumerate(lines) if 'aspis_r1_cost_probe::compact::check_values' in s)
(H/'failure-context.log').write_text('\n'.join(lines[max(0,idx-5):idx+15]+['[... intervening symbolic trace omitted ...]']+lines[-90:])+'\n')
