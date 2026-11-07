from NMX_formal import *
files={
 'NMX_217_prepare_host.py':(E/'NMX_217_prepare_host.py').read_text(),
 'NMX_217_native.rs':(E/'NMX_217_native.rs').read_text(),
 'NMX_217_reference.rs':Path('evidence/native-decref-20261028/NCV_reference.rs').read_text(),
 'NMX_KMX_copy_stubs.patch':Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text(),
 'NMX_217_gate.py':(E/'NMX_217_gate.py').read_text(),
 'NMX_frozen_graph.sha256':Path('evidence/native-decref-20261028/NCV_frozen_graph.sha256').read_text(),
}
r=run('NMX_L673','inspect','NMX_217_prepare',command=['python3','NMX_217_prepare_host.py'],extra=files)
assert r['exit_status']==0
# Retain generated patch and imported-object hashes without changing host state.
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{n:(b/n).read_text() for n in ['NMX_217_harness.patch','NMX_NCV_SEED.json']}}))
''');assert r.returncode==0,r.stderr
for n,s in json.loads(r.stdout).items():(E/n).write_text(s)
