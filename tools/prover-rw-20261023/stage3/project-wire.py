"""Project exact declarations from retained caller-005; never synthesize externals.
Run on host. The receipt pins the full emitted files and every projected block.
"""
from pathlib import Path
import hashlib,json
H=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023')
G=H/'src/generated-caller-005'; O=H/'stage3/projected-wire'; O.mkdir(exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
def select(file,name):
 s=(G/file).read_text(); blocks=s.split('/-- ')
 matches=[('/-- '+b).rstrip()+'\n' for b in blocks[1:] if ('\ndef '+name+'\n' in b or '\ndef '+name+' ' in b or '\nstructure '+name+' ' in b or '\ninductive '+name+' ' in b)]
 assert len(matches)==1,(name,len(matches))
 return matches[0]
types=['aspis_core.field.M31','aspis_core.field.CM31','aspis_core.field.QM31','aspis_core.digest.Digest32','r1_wire.Error','host_wire.SemanticTranscript']
funs=['host_wire.SemanticTranscript.sample_block_validated']
rows=[]
for file,names in [('Types.lean',types),('Funs.lean',funs)]:
 blocks=[select(file,n) for n in names]
 imports='import Aeneas\n' if file=='Types.lean' else 'import R1Z.ProverRwWireTypes\n'
 text=imports+'open Aeneas Aeneas.Std Result ControlFlow Error\nnamespace ProverRwWire\n\n'+'\n'.join(blocks)+'\nend ProverRwWire\n'
 (O/file).write_text(text)
 rows.append(dict(input=str(G/file),input_sha256=sha((G/file).read_bytes()),declarations=[dict(name=n,sha256=sha(b.encode())) for n,b in zip(names,blocks)],output_sha256=sha(text.encode())))
(O/'projection.json').write_text(json.dumps(dict(projection='Exact declaration blocks, only imports and enclosing namespace changed; no external template installed',rows=rows),indent=2)+'\n')
