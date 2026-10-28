from KNG_control import *
r=py(f'''from pathlib import Path
p=Path({B!r})/'KNG_src/Cargo.toml';s=p.read_text().replace('members = [','members = ["crates/aspis-prover",',1).replace('"crates/aspis-prover","programs"','"programs"');p.write_text(s)
''');assert r.returncode==0,r.stderr
rc=launch('KNG_I002','metadata',['python3','KNG_preflight.py','KNG_I002'],['KNG_preflight.py','KNG_src/Cargo.lock','KNG_src/Cargo.toml']);print(rc['exit_status'])
