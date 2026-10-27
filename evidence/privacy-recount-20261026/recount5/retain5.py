from pathlib import Path
import json,subprocess,hashlib,os
P=Path(__file__).resolve().parent;pins=json.loads((P/'pins.json').read_text())['revisions'];manifest=json.loads((P/'manifest.json').read_text());ix={(x['ref'],x['path']):x for x in manifest}
keep={tuple(x) for x in json.loads((P/'used-sources5.json').read_text())}
for a in json.loads((P/'definition-audit5.json').read_text()):
 keep.update((x['ref'],x['path']) for x in a['sources'])
for c in json.loads((P/'checks.json').read_text()):keep.add((c['pinned_ref'],c['pinned_path']))
extra=[('cblib','evidence/pv-cblib-20261027/RESUME8-RECEIPTS.json'),('cblib','evidence/pv-cblib-20261027/RESUME9-RECEIPTS.json'),('n7','evidence/pv-n7-20261027/patches/0001-private-key-raw-fd.patch'),('n7','evidence/pv-n7-20261027/INVENTORY.md'),('n7','evidence/pv-n7-20261027/resource-summary.json'),('batch1','evidence/pv-batch1-20261027/gate-a-resume.json'),('route2','design/PV-ROUTE2-20261027.md'),('research','docs/research/v8-r0-zk-20261009/LOG.md'),('research','design/RELEASE-LEDGER-20261025.md'),('cblib','design/PV-SHA-DISPATCH-20261027.md')]
reused=[]
for k,path in extra:
 keep.add((k,path))
 if (k,path) not in ix:
  q=subprocess.run(['git','show',pins[k]+':'+path],capture_output=True);assert q.returncode==0,(k,path,q.stderr)
  raw=q.stdout;blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest();out=P/'objects'/(blob+'.txt');out.write_bytes(raw)
  ix[k,path]=dict(ref=k,revision=pins[k],path=path,blob=blob,sha256=hashlib.sha256(raw).hexdigest(),snapshot=os.path.relpath(out,P))
 if path.endswith('.json'):reused.append(ix[k,path])
selected=[x for key,x in ix.items() if key in keep];selected.sort(key=lambda x:(x['ref'],x['path']));before=len(ix)
(P/'manifest.json').write_text(json.dumps(selected,indent=2)+'\n');(P/'reused-receipts5.json').write_text(json.dumps(dict(current=reused,prior='../recount4/reused-receipts4.json',scope='Original proof/gate receipts reused at immutable branch pins; not new worker runs.'),indent=2)+'\n')
kept={str((P/x['snapshot']).resolve()) for x in selected};removed=[]
for f in (P/'objects').glob('*.txt'):
 if str(f.resolve()) not in kept:removed.append(f.name);f.unlink()
(P/'retention5.json').write_text(json.dumps(dict(captured_records=before,retained_records=len(selected),unused_capture_objects_removed=len(removed),removed=removed,rule='Only unused recount5 git-object text snapshots removed; historical/research/branch sources and keys untouched.'),indent=2)+'\n')
print(before,'→',len(selected),'records;',len(removed),'unused snapshots removed')
