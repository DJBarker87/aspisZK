"""Reproduce the exact wrapper parameterization; never compile axiom templates."""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent
raw=E/'NMX_auth_box_emitted/raw/NMX_auth/Funs.lean'
s=raw.read_text();a=s.index('def\n  r1_pool_adapter.decode_master_box.closure.');b=s.index('/-- [aspis_r1_cost_probe_program::r1_pool_adapter::owned::',a)
x=re.sub(r'/\-\-.*?\-/','',s[a:b],flags=re.S)
x=x.replace('r1_pool_adapter.decode_master_box','master').replace('r1_pool_adapter.decode_checkpoint_box','checkpoint')
x=x.replace('aspis_statement.pool_v1.pair_forest_accounts.decode_pool_v1_pair_forest_master_v1','rawMaster').replace('aspis_statement.pool_v1.pair_forest_accounts.decode_pool_v1_pair_forest_checkpoint_v1','rawCheckpoint')
x=x.replace('def master\n','def master (rawMaster : Slice U8 → Result (core.result.Result NMX_OwnedPackets.Master NJQ_Carrier.CF))\n').replace('def checkpoint\n','def checkpoint (rawCheckpoint : Slice U8 → Result (core.result.Result NMX_OwnedPackets.Checkpoint NJQ_Carrier.CF))\n')
header='''import NMX_OwnedPackets
import NMX_MasterValue
import NMX_CheckpointValue
set_option autoImplicit false
noncomputable section
namespace NMX_R4_BoxEmitted
open Aeneas Aeneas.Std Result AdapterRw
abbrev master.closure := Unit
abbrev checkpoint.closure := Unit
'''
expected=header+x+'\nend NMX_R4_BoxEmitted\nend\n'
target=E/'NMX_R4_BoxEmitted.lean';assert target.read_text()==expected
raw_types=E/'NMX_auth_box_emitted/raw/NMX_auth/Types.lean';types=raw_types.read_text()
for name in ['master','checkpoint']:
 assert f'def r1_pool_adapter.decode_{name}_box.closure := Unit' in types
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report={'status':'PASS','exact_parameterization':True,'raw':str(raw.relative_to(E)),'raw_sha256':sha(raw),'types_sha256':sha(raw_types),'target':target.name,'target_sha256':sha(target),'changes':['namespace/definition renames','same-typed raw child callable parameters','canonical shared carriers via imports','Unit closure types exactly as emitted'],'axiom_templates_compiled':False}
(E/'NMX_R4_BOX_SOURCE_CHECK.json').write_text(json.dumps(report,indent=1)+'\n');print(json.dumps({'status':'PASS','target':target.name}))
