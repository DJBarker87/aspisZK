"""Remove only owned rebuildable scratch with verified retained exports/backups."""
from pathlib import Path
import json,lzma,hashlib,subprocess
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-slice-s-join-20261105'
pins=[]
for f in E.glob('NGI_NEP_*_REACHABLE.txt.xz'):
 raw=lzma.decompress(f.read_bytes());h=hashlib.sha256(raw).hexdigest();assert Path(str(f)[:-3]+'.sha256').read_text().strip()==h
 pins.append(dict(host_name=f.name.removeprefix('NGI_').removesuffix('.xz'),sha256=h,backup=f.name,compressed_sha256=hashlib.sha256(f.read_bytes()).hexdigest()))
assert len(pins)==3954
(E/'NGI_RAW_BACKUPS.json').write_text(json.dumps(pins,indent=1)+'\n')
export=json.loads((E/'NGI_EXPORT.json').read_text())
code='''from pathlib import Path
import json,hashlib,os
b=Path(B);removed=[]
for r in export['exports']:
 p=Path(r['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
 source=b/('NGI_objects' if p.parent.name=='NGI_exports_20261105' else 'NGI_native_IGNORED')/p.name
 if source.parent.name=='NGI_native_IGNORED':source=b/'NGI_native'/p.name
 if source.is_file():
  assert hashlib.sha256(source.read_bytes()).hexdigest()==r['sha256'];source.unlink();removed.append(str(source))
for r in pins:
 p=b/r['host_name']
 if p.exists():assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'];p.unlink();removed.append(str(p))
live=[]
for d in Path('/proc').iterdir():
 if not d.name.isdigit():continue
 try:args=(d/'cmdline').read_bytes().split(b'\\0');name=Path(args[0].decode()).name
 except (OSError,UnicodeDecodeError):continue
 if name in ['NGI_ProofDriver','NGI_Driver'] or (name=='lean' and any(b'NGI_generated' in a for a in args)):live.append(d.name)
assert not live,live
print(json.dumps(dict(removed_scratch_paths=len(removed),compiled_exports_retained=len(export['exports']),raw_backups=len(pins),own_cache_retained=True,live_prover_processes=live)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\npins='+repr(pins)+'\nexport='+repr(export)+'\n'+code,text=True,capture_output=True)
(E/'NGI_CLEANUP_TRANSPORT.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr;(E/'NGI_HOST_END.json').write_text(r.stdout);print(r.stdout)
