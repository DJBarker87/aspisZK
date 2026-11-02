"""Refresh the retained finite scanner on the adopted binary. No client execution."""
from pathlib import Path
import hashlib,json,subprocess,sys
D=Path(__file__).parent
B=Path('/home/dombarker/project-offloads/codex-pv-c474-20261029/native-target/client/devnet_spend')
expected='da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0'
assert hashlib.sha256(B.read_bytes()).hexdigest()==expected
P=D/'inputs/l3'
pins=json.loads((D/'PV_O11_l3-input-pins.json').read_text())
for x in pins.values():
    assert hashlib.sha256((D/x['snapshot']).read_bytes()).hexdigest()==x['sha256']
out=D/'l3-audit';out.mkdir(exist_ok=False)
# The old scanner is reused byte-for-byte. Controls locate its original filename.
for name in ['PV_L3A_audit.py','PV_L3A_controls.py']:
    (out/name).write_bytes((P/('pv-l3a-20261029-'+name)).read_bytes())
subprocess.run([sys.executable,str(out/'PV_L3A_controls.py')],check=True)
subprocess.run([sys.executable,str(out/'PV_L3A_audit.py'),str(out),str(B)],check=True)
s=json.loads((out/'summary.json').read_text())
assert s['binary_sha256']==expected
assert s['selected']>0 and s['functions']>0
assert not s['inline_completeness']
result=dict(classification='finite static evidence only; heuristic CLEAN is conditional, not a row restoration',
    scanner_reused_verbatim=True,client_executed=False,client_rebuilt=False,
    expected_binary_sha256=expected,summary=s,
    tools={k:subprocess.check_output([k,'--version'],text=True).splitlines()[0] for k in ['nm','objdump','readelf']},
    inputs={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),D/'PV_O11_l3_run.py',D/'PV_O11_l3-input-pins.json']},
    retained_boundaries=['V370','V371','full operand/caller and inline provenance','same native full observer'],
    restored=0,premises_removed=0,premises_added=0,premises_weakened=0)
(D/'PV_O11_l3-native-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(ok=True,selected=s['selected'],classifications=s['classifications'],restored=0)))
