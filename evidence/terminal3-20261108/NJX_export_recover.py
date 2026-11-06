from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent;config=json.loads((E/'NJX_L149.json').read_text());pins=json.loads((E/'NJX_L148/receipt.json').read_text())['deps_fingerprint']['selected_objects'];pins={k:v for k,v in pins.items()if '/Aeneas/'in k or '/AeneasMeta/'in k or k.endswith('/Aeneas.olean')}
code='''from pathlib import Path
import json,hashlib,shutil,sys
D=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJX_20261108');pins=json.load(sys.stdin)
files=[]
for p in sorted(D.rglob('*')):
 if p.is_file():files.append(dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
for p,x in pins.items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==x['sha256'],p
assert files
print(json.dumps(dict(export_dir=str(D),files=files,bytes=sum(x['bytes']for x in files),library_pins=list(pins.values()),disk_free=shutil.disk_usage(D).free)))
'''
# code goes through -c argv; pinned dictionary through stdin. This reads only.
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3 -c '+__import__('shlex').quote(code)],input=json.dumps(pins),text=True,capture_output=True)
(E/'NJX_EXPORT_RECOVERY_TRANSPORT.json').write_text(json.dumps(dict(exit_status=r.returncode,stderr=r.stderr,read_only=True,no_build=True)))
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);D=Path(x['export_dir']);B=Path('/home/dombarker/project-offloads/codex-cx-terminal3-20261108');paths=[str(D/Path(p).name)if Path(p).parent==B else p for p in config['env']['LEAN_PATH'].split(':')]
x.update(status='RETAINED_READ_ONLY_MANIFEST_RECOVERY',source_revision=config['source_revision'],LEAN_PATH=':'.join(paths),cache_retained=True,original_export_scope='NJX_L149',original_exit_status=1,read_only_recovery=True,no_formal_rerun=True,CARGO_TARGET_DIR=str(B/'NJX_target'),library_pin_rule='all selected individual Aeneas/AeneasMeta objects from L148 receipt; no assumed umbrella',seed_order=['NJL','NJO'])
(E/'NJX_EXPORT.json').write_text(json.dumps(x,indent=1));print('Retained export and library pins read-only verified:',x['bytes'],'bytes')
