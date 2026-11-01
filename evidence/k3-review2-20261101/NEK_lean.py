from NEK_host import *
from NEK_scan import sha
W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
def setup():
 admit('NEK_LEAN_SETUP')
 r=py(f'''from pathlib import Path
import shutil,json,hashlib
b=Path({B!r});w=Path({W!r});copied={{}}
for n in ['lakefile.toml','lean-toolchain','lake-manifest.json']:
 p=w/n;shutil.copy2(p,b/n);copied[n]=hashlib.sha256(p.read_bytes()).hexdigest()
(b/'.lake').mkdir(exist_ok=True)
p=b/'.lake/packages'
if not p.exists():p.symlink_to(w/'.lake/packages',target_is_directory=True)
for n,t in { {n:(E/n).read_text() for n in ['NEK_ByteWindows.lean','NEK_lean_gate.py']}!r}.items():(b/n).write_text(t)
print(json.dumps(copied))
''');assert r.returncode==0,r.stderr;(E/'NEK_LEAN_CONFIG_PINS.json').write_text(r.stdout)
def run():
 setup()
 cfg=dict(attempt='NEK_L001',kind='lean',module='NEK_ByteWindows.lean',sources=['NEK_ByteWindows.lean','NEK_lean_gate.py','lakefile.toml','lean-toolchain','lake-manifest.json'],command=['python3','NEK_lean_gate.py'],env=dict(PATH='/home/dombarker/.elan/bin:/home/dombarker/.cargo/bin:/usr/bin:/bin',LEAN_PATH='/home/dombarker/project-offloads/codex-cx-k3-review2-cache-20261029:'+W+'/objects:'+W),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint=dict(coherent_workspace=W,config_pins_sha256=sha((E/'NEK_LEAN_CONFIG_PINS.json').read_bytes()),cache_imports_sha256=sha((E/'NEK_CACHE_IMPORTS.json').read_bytes())),expected_time='focused generic Nat quotient/remainder assembly, no generated recurrence or cold dependency build',print_axioms=['NEK_ByteWindows.quotient_remainder_ext','NEK_ByteWindows.indexed_nibbles_ext'])
 rc=launch(cfg)
 r=py(f"from pathlib import Path;print((Path({B!r})/'NEK_L001_LIBRARY_PINS.json').read_text())");assert r.returncode==0;(E/'NEK_L001_LIBRARY_PINS.json').write_text(r.stdout)
if __name__=='__main__':run()
