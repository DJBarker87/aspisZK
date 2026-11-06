from NJH_formal import *
extra={'NJH_ref/Cargo.toml':(E/'NJH_Cargo.toml').read_text(),'NJH_ref/src/lib.rs':(E/'NJH_reference.rs').read_text(),'NJH_extract_host.py':(E/'NJH_extract_host.py').read_text()}
r=run('NJH_L003','extract','NJH_Ref',command=['python3','NJH_extract_host.py'],extra=extra,env_extra={'CARGO_TARGET_DIR':B+'/NJH_target'})
r=ssh('python3',f"from pathlib import Path;import json;b=Path({B!r});paths=[b/'NJH_EXTRACTION_PINS.json',b/'NJH_EXTRACTION_LAUNCHED.json']+list((b/'NJH_extracted').rglob('*.lean'));print(json.dumps({{str(p.relative_to(b)):p.read_text() for p in paths if p.is_file()}}))")
assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
