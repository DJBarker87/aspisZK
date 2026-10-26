"""Pin literal frozen-source integer constant initializers; no native ABI claim."""
from pathlib import Path
import json,re,hashlib,sys
r=Path(__file__).resolve().parents[3]
rows=[(82,'crates/aspis-core/src/r0/merkle.rs','C1_TAG','u8'),(83,'crates/aspis-core/src/r0/merkle.rs','C2_TAG','u8'),(86,'crates/aspis-core/src/r0/opening.rs','LANES','usize'),(111,'crates/aspis-core/src/state_only_hiding.rs','PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT','u64')]
entries=[];pins=[]
for i,path,name,ty in rows:
 s=(r/path).read_text();m=re.search(r'pub const '+name+r': '+ty+r' = ([0-9a-fx_]+);',s);assert m,name
 v=int(m[1].replace('_',''),0);entries.append((i,ty,v));pins.append(dict(entry=i,path=path,source_sha256=hashlib.sha256(s.encode()).hexdigest(),declaration=m[0],value=v))
b='''import R1Z.ProverRwDictionaryEmbedding
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryConstants
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwDictionaryEmbedding.selected ops with
'''+ '\n'.join(f'    op{i} := .ok {v}#{t}'+('}' if j==len(entries)-1 else '') for j,(i,t,v) in enumerate(entries))+'\n\n'+ '\n'.join(f'theorem entry{i} (ops : ExternalFuns) : (selected ops).op{i} = .ok {v}#{t} := rfl\n#print axioms entry{i}\n' for i,t,v in entries)+'\nend R1Z.ProverRwDictionaryConstants\n'
o=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwDictionaryConstants.lean'
if '--check' in sys.argv:assert o.read_text()==b
else:
 o.write_text(b);(r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/native-install/constant-source.json').write_text(json.dumps(dict(initializers=pins,output_sha256=hashlib.sha256(b.encode()).hexdigest(),scope='Literal source integer initializers; no native whole dictionary representation or callback assertion.'),indent=2)+'\n')
