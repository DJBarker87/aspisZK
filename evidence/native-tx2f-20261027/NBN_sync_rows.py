from pathlib import Path
import importlib.util,sys,json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;sys.argv=['sync','none']
s=importlib.util.spec_from_file_location('NBN_native',E/'NBN_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
m.admit('NBN_ROW_SYNC');source=(E/'NBN_more.rs.txt').read_text();oldhash=json.loads((E/'NBN_LATE_SYNC.json').read_text())['source_hash']
lib='crates/aspis-statement/src/lib.rs';oldlib=subprocess.check_output(['git','show',m.REV+':'+lib],text=True);attr='#![cfg_attr(kani, feature(iter_next_index))]\n'
r=m.py(f'''from pathlib import Path
import hashlib,json
b=Path({m.B!r})/'NBN_src';p=b/'crates/aspis-statement/src/pool_v1/NBN_more.rs'
assert hashlib.sha256(p.read_bytes()).hexdigest()=={oldhash!r}
q=b/{lib!r};assert hashlib.sha256(q.read_bytes()).hexdigest()=={hashlib.sha256(oldlib.encode()).hexdigest()!r}
p.write_text({source!r});q.write_text({attr!r}+q.read_text())
print(json.dumps(dict(harness_hash=hashlib.sha256(p.read_bytes()).hexdigest(),lib_hash=hashlib.sha256(q.read_bytes()).hexdigest())))
''');assert r.returncode==0,r.stdout+r.stderr
(E/'NBN_ROW_SYNC.json').write_text(r.stdout)
path='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';old=subprocess.check_output(['git','show',m.REV+':'+path],text=True);inc='\n#[cfg(kani)]\n#[path="NBN_more.rs"]\nmod NBN_more;\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),(old+inc).splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+=''.join(difflib.unified_diff(oldlib.splitlines(True),(attr+oldlib).splitlines(True),fromfile='a/'+lib,tofile='b/'+lib))
patch+=''.join(difflib.unified_diff([],source.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-statement/src/pool_v1/NBN_more.rs'))
(E/'NBN_control_rows.patch').write_text(patch)
