"""Read-only frozen scratch audit; no compiler, resolver, or prover is run."""
from pathlib import Path
import hashlib,json,zlib,base64,sys,importlib.util,subprocess
E=Path(__file__).resolve().parent
frozen=json.loads(Path('evidence/native-tx2k-20261028/NBX_FROZEN_SOURCE_AUDIT.json').read_text());expected=frozen['frozen_hashes']
receipt=json.loads((E/'NCC_K060/receipt.json').read_text())
allowed=['crates/aspis-statement/src/lib.rs','crates/aspis-statement/src/pool_v1/pair_terminal.rs','crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs','crates/aspis-statement/src/pool_v1/verifier_registry.rs']
other={n:h for n,h in expected.items() if n not in allowed};digest=hashlib.sha256(json.dumps(other,sort_keys=True,separators=(',',':')).encode()).hexdigest()
x=dict(names=list(expected),allowed={n:receipt['source_hashes']['NBU_src/'+n] for n in allowed},other_digest=digest,root={n:hashlib.sha256(Path(n).read_bytes()).hexdigest() for n in ['Cargo.toml','Cargo.lock']},NCC_module=receipt['source_hashes']['NBU_src/crates/aspis-statement/src/pool_v1/NCC_slots.rs'])
encoded=base64.b64encode(zlib.compress(json.dumps(x).encode(),9)).decode()
sys.argv=['ncc','none'];s=importlib.util.spec_from_file_location('ncc',E/'NCC_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
code='''from pathlib import Path
import hashlib,json,base64,zlib
b=Path(%r)/'NBU_src';x=json.loads(zlib.decompress(base64.b64decode(%r)))
actual={n:hashlib.sha256((b/n).read_bytes()).hexdigest() for n in x['names']}
other={n:h for n,h in actual.items() if n not in x['allowed']};digest=hashlib.sha256(json.dumps(other,sort_keys=True,separators=(',',':')).encode()).hexdigest();assert digest==x['other_digest'],'frozen scratch drift'
assert all(actual[n]==h for n,h in x['allowed'].items()),'cfg-instrumented parent differs from native receipt'
assert all(hashlib.sha256((b/n).read_bytes()).hexdigest()==h for n,h in x['root'].items()),'root Cargo/lock drift'
assert hashlib.sha256((b/'crates/aspis-statement/src/pool_v1/NCC_slots.rs').read_bytes()).hexdigest()==x['NCC_module'],'own native module differs'
print(json.dumps(dict(frozen_files=len(actual),unmodified_default_files=len(other),unmodified_canonical_sha256=digest,cfg_instrumented_parent_hashes=x['allowed'],all_match_frozen_or_exact_native_receipt=True,root_cargo_lock_unchanged=True,NCC_module_sha256=x['NCC_module'],no_prover_run=True)))
'''%(m.B,encoded)
r=m.py(code);assert r.returncode==0,r.stdout+r.stderr
(E/'NCC_HOST_SOURCE_AUDIT.json').write_text(r.stdout);print(r.stdout)
