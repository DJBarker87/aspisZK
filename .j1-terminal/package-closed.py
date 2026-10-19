from pathlib import Path
import json,hashlib,tarfile,io
w=Path(__file__).resolve().parent;repo=w.parent
out=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-closed-cone-432-20261016';out.mkdir(parents=True,exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
modules=['AspisR1TerminalValidator.Types','AspisR1TerminalValidator.FunsExternal','AspisR1TerminalValidator.Funs','TerminalGeneratedAudit','ExtractedTerminalEquality']
attempts=['types-a','funs-a','funs-b','equality-a','equality-b','equality-c']
files={}
def add(p):
 if p.is_file() and not p.is_symlink(): files[str(p.relative_to(w))]=p.read_bytes()
for top in ['original','compat-inputs']:
 for p in (w/top).rglob('*'):add(p)
for p in [w/'runner.py',w/'option-discriminant-source.json']:add(p)
for label in attempts:
 for p in (w/'runs'/label).rglob('*'):add(p)
records={}
for name in modules:
 p=w/'sources'/(name.replace('.','/')+'.lean');add(p)
 rp=w/'successful-targets'/(name+'.json');add(rp);r=json.loads(rp.read_text())
 assert r['exit_status']==0 and r['axioms']['passed'] and r['key']['source_sha256']==sha(p.read_bytes())
 for suf,obj in r['objects'].items():
  op=w/'objects'/(name.replace('.','/')+suf);assert sha(op.read_bytes())==obj['sha256'];add(op)
 records[name]={'source_sha256':sha(p.read_bytes()),'receipt':str(rp.relative_to(w)),'wall_seconds':r['wall_seconds'],'sampled_cgroup_peak_bytes':r['sampled_cgroup_peak_bytes'],'peak_process_rss_kib':r['peak_process_rss_kib'],'process_swaps':r['process_swaps'],'axioms':r['axioms']}
checks=''.join(f'{sha(b)}  {n}\n' for n,b in sorted(files.items())).encode();files['SHA256SUMS']=checks
archive=out/'checked-sources-receipts-objects.tar.gz'
with tarfile.open(archive,'w:gz') as tf:
 for n,b in sorted(files.items()):
  info=tarfile.TarInfo(n);info.size=len(b);info.mode=0o644;info.mtime=0;tf.addfile(info,io.BytesIO(b))
manifest={'format':1,'scope':'Five checked modules only; terminal withdrawal success theorem excluded. Original opaque template is evidence only, not imported. Exact generated Types/Funs are mirrored by coordinator commit ddcaa068e2d964a09b69ea204e54bc000402364a.', 'rust_source_revision':'42e5ca2011c39ee9770afc798282ff861b092428','archive':archive.name,'archive_sha256':sha(archive.read_bytes()),'archive_entries':len(files),'modules':records,'retained_attempts':attempts,'standard_only_report_count':11,'no_full_replay':True,'generated_byte_changes':False}
(out/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
(out/'SHA256SUMS').write_text(''.join(f'{sha(p.read_bytes())}  {p.name}\n' for p in [archive,out/'manifest.json']))
print(json.dumps({'entries':len(files),'bytes':archive.stat().st_size,'sha256':sha(archive.read_bytes())},indent=2))
