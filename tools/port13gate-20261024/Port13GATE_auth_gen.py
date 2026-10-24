from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(L/'Port11PROV_Authenticated.lean').read_text()
s=s.replace('import Port6AUTH_Recovery','import Port6AUTH_Recovery\nimport Port13GATE_Canonical')
s=s.replace('namespace AspisR1.Port11PROV_Authenticated','namespace AspisR1.Port13GATE_Authenticated').replace('end AspisR1.Port11PROV_Authenticated','end AspisR1.Port13GATE_Authenticated')
a=s.index('    (binary :');b=s.index('    (sourceAccepted',a)
s=s[:a]+'''    (occupiedGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) occupied)
    (siblingGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) sibling)
    (leafGate : MultiproofConeP6Batch.LeafGate H leaf)
'''+s[b:]
s=s.replace('p6.occupied_parent p6.sibling_parent p6.leaf','occupiedGate siblingGate leafGate')
a=s.index('  have frozen :=');b=s.index('  have accepted0',a)
s=s[:a]+'''  have frozen := Port13GATE_Canonical.both_batches H occupied sibling leaf
    occupiedGate siblingGate leafGate parsed q nodes views
'''+s[b:]
target=L/'Port13GATE_Authenticated.lean'
if '--check' in sys.argv:
 assert target.read_text()==s,'Generated consumer drift'
 print('Exact old consumer retained except namespace/import and explicit gate/canonical substitutions')
else:target.write_text(s)
