from pathlib import Path
import importlib.util,sys,json
E=Path(__file__).resolve().parent;sys.argv=['cleanup','none'];s=importlib.util.spec_from_file_location('native',E/'NBX_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
r=m.py(f'''from pathlib import Path
import hashlib,json,os,shutil
b=Path({m.B!r});cache=Path('/home/dombarker/project-offloads/codex-cx-tx2codec-cache-20261028')
active=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:
  exe=Path(os.readlink(p/'exe')).name;cmd=(p/'cmdline').read_bytes().replace(b'\\x00',b' ').decode(errors='replace');cwd=str((p/'cwd').resolve())
 except (OSError,PermissionError):continue
 if exe in ['cbmc','kani-driver','cargo-kani','rustc','cargo','lean','timeout'] and (str(b) in cmd or cwd.startswith(str(b))):active.append(dict(pid=p.name,exe=exe,cmd=cmd))
assert not active,active
pins=json.loads((b/'NBX_CACHE_IMPORTED.json').read_text());end={{str(p.relative_to(cache)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in cache.rglob('*') if p.is_file()}}
assert all(end.get(n)==v for n,v in pins.items()),'imported cache changed'
lib=json.loads((b/'NBX_LIBRARY_PIN.json').read_text())
assert all(hashlib.sha256(Path(n).read_bytes()).hexdigest()==v['sha256'] for n,v in lib.items()),'Aeneas pin changed'
last=json.loads((b/'NBX_K050/receipt.json').read_text())
assert all(hashlib.sha256((b/n).read_bytes()).hexdigest()==v for n,v in last['source_hashes'].items()),'final native source changed'
removed=[]
for n in ['NBX_target','NBX_tmp']:
 p=b/n
 if p.exists():
  size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file());removed.append(dict(path=str(p),bytes=size));shutil.rmtree(p)
report=dict(active_own_provers=active,cache_retained=str(cache),imported_cache_files=len(pins),final_cache_files=len(end),all_imported_hashes_unchanged=True,Aeneas_pins_unchanged=len(lib),final_native_source_hashes_match=True,removed=removed,source_and_receipts_retained=str(b),wallet_operations='none')
(b/'NBX_CACHE_END.json').write_text(json.dumps(end,indent=2));(b/'NBX_CLEANUP.json').write_text(json.dumps(report,indent=2))
print(json.dumps(dict(report=report,cache_end=end)))
''');assert r.returncode==0,r.stdout+r.stderr
x=json.loads(r.stdout)
for k,n in [('report','NBX_CLEANUP.json'),('cache_end','NBX_CACHE_END.json')]: (E/n).write_text(json.dumps(x[k],indent=2)+'\n')
print(json.dumps(x['report']))
