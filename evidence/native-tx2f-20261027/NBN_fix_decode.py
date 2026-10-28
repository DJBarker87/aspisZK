from pathlib import Path
import sys,importlib.util,json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;sys.argv=['fix','none']
s=importlib.util.spec_from_file_location('NBN_native',E/'NBN_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
m.admit('NBN_DECODE_FIX');expected=json.loads((E/'NBN_DECODE_SYNC.json').read_text())['harness_sha256'];source=(E/'NBN_decode.rs.txt').read_text()
r=m.py(f'''from pathlib import Path
import hashlib,json
p=Path({m.B!r})/'NBN_src/crates/aspis-statement/src/pool_v1/NBN_decode.rs'
assert hashlib.sha256(p.read_bytes()).hexdigest()=={expected!r}
p.write_text({source!r});print(json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest())))
''');assert r.returncode==0,r.stdout+r.stderr
(E/'NBN_DECODE_FIX.json').write_text(r.stdout)
path='crates/aspis-statement/src/pool_v1/pair_terminal.rs';old=subprocess.check_output(['git','show',m.REV+':'+path],text=True);inc='\n#[cfg(kani)]\n#[path="NBN_codecs.rs"]\nmod NBN_codecs;\n\n#[cfg(kani)]\n#[path="NBN_decode.rs"]\nmod NBN_decode;\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),(old+inc).splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+=''.join(difflib.unified_diff([],source.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-statement/src/pool_v1/NBN_decode.rs'))
(E/'NBN_decode_fixed.patch').write_text(patch)
