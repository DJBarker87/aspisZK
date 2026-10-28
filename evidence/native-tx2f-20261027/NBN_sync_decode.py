from pathlib import Path
import sys,importlib.util,json,hashlib,subprocess
E=Path(__file__).resolve().parent;sys.argv=['sync','none']
s=importlib.util.spec_from_file_location('NBN_native',E/'NBN_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
m.admit('NBN_DECODE_SYNC');path='crates/aspis-statement/src/pool_v1/pair_terminal.rs';old=subprocess.check_output(['git','show',m.REV+':'+path],text=True);oldinc='\n#[cfg(kani)]\n#[path="NBN_codecs.rs"]\nmod NBN_codecs;\n';inc='\n#[cfg(kani)]\n#[path="NBN_decode.rs"]\nmod NBN_decode;\n';source=(E/'NBN_decode.rs.txt').read_text()
r=m.py(f'''from pathlib import Path
import hashlib,json
b=Path({m.B!r})/'NBN_src';p=b/{path!r}
assert hashlib.sha256(p.read_bytes()).hexdigest()=={hashlib.sha256((old+oldinc).encode()).hexdigest()!r}
p.write_text(p.read_text()+{inc!r});q=b/'crates/aspis-statement/src/pool_v1/NBN_decode.rs';assert not q.exists();q.write_text({source!r})
print(json.dumps(dict(parent_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(q.read_bytes()).hexdigest())))
''');assert r.returncode==0,r.stdout+r.stderr
(E/'NBN_DECODE_SYNC.json').write_text(r.stdout)
