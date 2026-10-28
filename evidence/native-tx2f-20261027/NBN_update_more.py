from pathlib import Path
import sys,importlib.util,json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;label=sys.argv[1];spec=json.loads((E/sys.argv[2]).read_text());sys.argv=['update','none']
s=importlib.util.spec_from_file_location('NBN_native',E/'NBN_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
m.admit(label);source=(E/spec['source']).read_text()
r=m.py(f'''from pathlib import Path
import hashlib,json
p=Path({m.B!r})/'NBN_src/crates/aspis-statement/src/pool_v1/NBN_more.rs'
assert hashlib.sha256(p.read_bytes()).hexdigest()=={spec['previous_sha256']!r}
p.write_text({source!r});print(json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)))
''');assert r.returncode==0,r.stdout+r.stderr
(E/(label+'.json')).write_text(r.stdout)
base='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';b=subprocess.check_output(['git','show',m.REV+':'+base],text=True);inc='\n#[cfg(kani)]\n#[path="NBN_more.rs"]\nmod NBN_more;\n'
lib='crates/aspis-statement/src/lib.rs';l=subprocess.check_output(['git','show',m.REV+':'+lib],text=True);attr='#![cfg_attr(kani, feature(next_index))]\n'
patch=''.join(difflib.unified_diff(b.splitlines(True),(b+inc).splitlines(True),fromfile='a/'+base,tofile='b/'+base))
patch+=''.join(difflib.unified_diff(l.splitlines(True),(attr+l).splitlines(True),fromfile='a/'+lib,tofile='b/'+lib))
patch+=''.join(difflib.unified_diff([],source.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-statement/src/pool_v1/NBN_more.rs'))
(E/(label+'.patch')).write_text(patch)
