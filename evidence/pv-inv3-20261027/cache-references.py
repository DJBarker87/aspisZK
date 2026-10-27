import pathlib,json
B=pathlib.Path('/home/dombarker/project-offloads/codex-pv-inv-20261027/inv3/objects');B.mkdir(parents=True,exist_ok=True)
for name in ['readonly-root-links.json','readonly-object-links.json']:
 for row in json.load(open('/home/dombarker/project-offloads/codex-pv-inv-20261027/inv2/'+name)):
  dst=pathlib.Path(row.get('path',str(B/row.get('module','').replace('.','/'))+'.olean').replace('/inv2/','/inv3/'))
  target=pathlib.Path(row['target'])
  if target.exists() and not dst.exists():
   dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(target)
