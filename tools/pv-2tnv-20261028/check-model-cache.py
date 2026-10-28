from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent;x=json.load(open(B/'model-resolution.json'));out=[]
env=json.load(open('/home/dombarker/project-offloads/codex-pv-runjoin-20261026/runjoin24-lean/J.json'));roots=[B/'objects',Path('/home/dombarker/project-offloads/codex-pv-runjoin-20261026/runjoin16-lean/std-cache')]+[Path(p) for p in env['LEAN_PATH'].split(':')]
for m,v in x['resolved'].items():
 c=v['cache'];rel=m.replace('.','/')+'.olean';o=next((r/rel for r in roots if (r/rel).is_file()),Path(c['object_path']));s=Path(c['source_path']);h=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest() if p.is_file() else None
 expected_object=c.get('object_expected_sha256',c['object_sha256']);os=h(o);ss=h(s)
 if ss is None and v.get('recorded_source_receipts'):ss=v['sha256']
 out.append(dict(module=m,object_path=str(o),object_sha256=os,expected_object=expected_object,source_path=str(s),source_sha256=ss,expected_source=v['sha256'],match=os==expected_object and ss==v['sha256']))
(B/'model-cache-check.json').write_text(json.dumps(out,indent=2)+'\n');bad=[r for r in out if not r['match']];print('project checked',len(out),'bad',len(bad));print(json.dumps(bad[:15]))
