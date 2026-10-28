from pathlib import Path
import importlib.util,sys,json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;sys.argv=['sync','none']
s=importlib.util.spec_from_file_location('NBN_native',E/'NBN_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
a='NBN_LATE_SYNC';m.admit(a)
source=(E/'NBN_more.rs.txt').read_text();oldhash=json.loads((E/'NBN_CONTROL_SYNC.json').read_text())['harness_hash']
r=m.py(f'''from pathlib import Path
import hashlib,json
p=Path({m.B!r})/'NBN_src/crates/aspis-statement/src/pool_v1/NBN_more.rs'
assert hashlib.sha256(p.read_bytes()).hexdigest()=={oldhash!r},'own previous source mismatch'
p.write_text({source!r});print(json.dumps(dict(source_hash=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)))
''');assert r.returncode==0,r.stdout+r.stderr
(E/(a+'.json')).write_text(r.stdout)
path='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';old=subprocess.check_output(['git','show',m.REV+':'+path],text=True);inc='\n#[cfg(kani)]\n#[path="NBN_more.rs"]\nmod NBN_more;\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),(old+inc).splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+=''.join(difflib.unified_diff([],source.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-statement/src/pool_v1/NBN_more.rs'))
(E/'NBN_control_latest.patch').write_text(patch)
