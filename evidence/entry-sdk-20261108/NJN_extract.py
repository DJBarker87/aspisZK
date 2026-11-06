from NJN_formal import *
extra={'NJN_ref/Cargo.toml':'[package]\nname="njn-reference"\nversion="0.1.0"\nedition="2021"\n[lib]\npath="src/lib.rs"\n[workspace]\n','NJN_ref/src/lib.rs':(E/'NJN_reference.rs').read_text(),'NJN_extract_host.py':(E/'NJN_extract_host.py').read_text()}
r=run('NJN_L001','extract','NJN_Ref',command=['python3','NJN_extract_host.py'],extra=extra)
r=ssh('python3',f"from pathlib import Path;import json;b=Path({B!r});paths=[b/'NJN_EXTRACTION_PINS.json',b/'NJN_EXTRACTION_LAUNCHED.json']+list((b/'NJN_extracted').rglob('*.lean'));print(json.dumps({{str(p.relative_to(b)):p.read_text() for p in paths if p.is_file()}}))")
assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
print('NJN extraction receipts recovered')
