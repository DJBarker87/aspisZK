from pathlib import Path
exec(Path(__file__).with_name('d347-small-packages.py').read_text().split("package('D026'")[0])
p=next(p for p in ps if p['index']==171);r=rs[p['receipt_blob']];package('D044',[171],'/home/dombarker/project-offloads/codex-pv-cbmid-20261027/source-proof',{f:pinned(h['sha256']) for f,h in r['source_snapshots'].items()},'Exact original per-run source_snapshots; classifier_all_usize was introduced after classifier_complete')
T=json.loads((C/'tree-index.json').read_text());tree={k:v for t in T.values() for k,v in t.items()}
for name,i,orig in [('D045',177,'/home/dombarker/project-offloads/codex-pv-join-20261026/pole4'),('D046',181,'/home/dombarker/project-offloads/codex-pv-join-20261026/direct5')]:
 p=next(p for p in ps if p['index']==i);parent=p['receipt'].rsplit('/',1)[0];overrides={}
 for k,b in tree.items():
  if k.startswith(parent+'/') and k.endswith(('.rs.txt','.toml.txt','.lock.txt')):overrides[Path(k).name[:-4]]=dict(text=subprocess.check_output(['git','cat-file','blob',b],text=True),origin=k,kind='committed original per-run snapshot',blob=b)
 package(name,[i],orig,overrides,'Exact committed per-run snapshots: helper added after earlier PASS in same family')
(E/'d347-plans.json').write_text(json.dumps(plans,indent=2)+'\n');(E/'d347-source-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n');(C/'d347-finish-payload.json').write_text(json.dumps(payload))
