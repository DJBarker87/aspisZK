from pathlib import Path
import sys,importlib.util,json,difflib,subprocess,hashlib
E=Path(__file__).resolve().parent
sys.argv=['sync','none']
s=importlib.util.spec_from_file_location('NBN_native',E/'NBN_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
m.admit('NBN_CONTROL_SYNC')
source=(E/'NBN_more.rs.txt').read_text()
path='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'
old=subprocess.check_output(['git','show',m.REV+':'+path],text=True)
inc='\n#[cfg(kani)]\n#[path="NBN_more.rs"]\nmod NBN_more;\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),(old+inc).splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+=''.join(difflib.unified_diff([],source.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-statement/src/pool_v1/NBN_more.rs'))
(E/'NBN_control.patch').write_text(patch)
r=m.py(f'''from pathlib import Path
import hashlib,json
b=Path({m.B!r})/'NBN_src';p=b/{path!r}
assert hashlib.sha256(p.read_bytes()).hexdigest()=={hashlib.sha256(old.encode()).hexdigest()!r},'frozen caller changed'
p.write_text(p.read_text()+{inc!r});(b/'crates/aspis-statement/src/pool_v1/NBN_more.rs').write_text({source!r})
print(json.dumps(dict(source_hash=hashlib.sha256(p.read_bytes()).hexdigest(),harness_hash=hashlib.sha256((b/'crates/aspis-statement/src/pool_v1/NBN_more.rs').read_bytes()).hexdigest())))
''')
assert r.returncode==0,r.stdout+r.stderr
(E/'NBN_CONTROL_SYNC.json').write_text(r.stdout)
