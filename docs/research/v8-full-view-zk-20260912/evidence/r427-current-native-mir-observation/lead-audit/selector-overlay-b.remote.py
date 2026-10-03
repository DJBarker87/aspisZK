import pathlib,sys,hashlib,json
root=pathlib.Path('/home/dombarker/project-offloads/aspis-r427-raw-mir-observer-20261002-a')
p=root/'charon/src/bin/charon-driver/translate/get_mir.rs'
a=root/'candidate-audit/selector-overlay-b'
assert not a.exists()
b=p.read_bytes(); assert hashlib.sha256(b).hexdigest()=='246d1fec2223d8ad5755e4aa9f24e647af7c16a18a8a2d893d9085213bf8a9ab'
new=sys.stdin.buffer.read(); assert hashlib.sha256(new).hexdigest()=='1013364396ff23f0ce80fcd31561ef0018126c01f445cbbd85fc5d95bc66322f'
assert hashlib.sha256((root/'observer-bin/charon-driver').read_bytes()).hexdigest()=='a7911f86aa775e99e685cc7d1c09e894e6e30c07dc65e83dd21ac0555ef08318'
a.mkdir(); (a/'get_mir.before-selector.rs').write_bytes(b); (a/'get_mir.selector.rs').write_bytes(new)
p.write_bytes(new)
d={'old_sha256':hashlib.sha256(b).hexdigest(),'new_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'old_driver_unchanged':True,'boundary':'isolated diagnostic selector only; original Charon and verifier not changed'}
(a/'receipt.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d))
