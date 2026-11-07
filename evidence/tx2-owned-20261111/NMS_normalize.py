"""Canonical-owner replay of fresh E003 definitions; no template axiom imported.
Every textual external replacement is retained in NMS_NORMALIZATION.json.
"""
from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
raw=(E/'NMS_extract_stage2/raw/NMS_stage2/Funs.lean').read_text()
sha=lambda t:hashlib.sha256(t.encode()).hexdigest()
base='r1_pool_adapter.owned.'
def definition(name):
 p=raw.index('def '+name+'\n');end=raw.find('\n/--',p)
 if end<0:end=raw.index('\nend NMS_stage2',p)
 return raw[p:end].strip()
changes={
 'solana_program_error.ProgramError.Insts.CoreCloneClone.clone':'ops.op35',
 'aspis_statement.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_v1':'ops.op23',
 'r1_pool_adapter.pool_program_id':'ops.op45',
 'solana_pubkey.Pubkey.new_from_array':'ops.op37',
 'aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1.nullifier':'ops.op20',
 'aspis_statement.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1':'ops.op17',
 'r1_pool_adapter.owned.authenticate_asq8_accounts':'auth',
 'core.slice.Slice.first':'ops.op9',
 'r1_pool_adapter.scan_proof_buffer':'ops.op51',
 'r1_pool_adapter.reconstruct_asq8_statement':'ops.op52',
 'aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1':'ops.op22',
 'aspis_r1_cost_probe.verifier.candidate.tx2_authenticated':'ops.op11',
 'r1_pool_adapter.emit_result':'ops.op53',
 '(error)':'(ops.op44)',
 'SolanaDigest.Insts.Aspis_coreDigestDigest32':'(SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)',
 'core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice\n        Std.U8':'core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice ops\n        Std.U8',
 'core.option.Option.Insts.CoreCmpPartialEqOption\n        (core.cmp.PartialEqShared':'core.option.Option.Insts.CoreCmpPartialEqOption ops\n        (core.cmp.PartialEqShared',
 'aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES':'(aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops)',
 'aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES':'(aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES ops)',
 'let o2 ← observer':'let o2 ← (observer ops)',
}
common='''set_option autoImplicit false
noncomputable section
namespace NMS_Emitted
open Aeneas Aeneas.Std Result AdapterRw
abbrev AuthCall := solana_pubkey.Pubkey → Slice r1_pool_adapter.owned.OwnedAccount →
 solana_pubkey.Pubkey → U8 → U64 → Result (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts solana_program_error.ProgramError)
'''
outputs={}
for fname,name in [('NMS_EmittedGetter','OwnedAccount.data'),('NMS_EmittedValidate','validate_asq8'),('NMS_Emitted241','stage2_owned')]:
 s=definition(base+name)
 for a,b in sorted(changes.items(),key=lambda p:-len(p[0])):s=s.replace(a,b)
 s=s.replace('r1_pool_adapter.owned.OwnedAccount.data','(get ops)').replace('def (get ops)','def get (ops : Ops)')
 s=s.replace('r1_pool_adapter.owned.validate_asq8 program_id','validate ops auth program_id')
 target={'OwnedAccount.data':'get','validate_asq8':'validate','stage2_owned':'stage2'}[name]
 if target!='get':s=s.replace('def '+base+name+'\n','def '+target+' (ops : Ops) (auth : AuthCall)\n',1)
 # Opaque external constant is interpreted by its frozen literal value.
 if target=='stage2':
  magic='aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC'
  s=s.replace('let a ←\n      '+magic,'let a ←\n      (pure '+magic+' : Result (Array U8 4#usize))')
 imp={'get':'AdapterRwModel','validate':'NMS_EmittedGetter','stage2':'NMS_EmittedValidate'}[target]
 pre=common if target=='get' else common[common.index('set_option'):common.index('abbrev AuthCall')]
 text='import '+imp+'\n'+pre+s+'\nend NMS_Emitted\n'
 (E/(fname+'.lean')).write_text(text);outputs[fname]={'sha256':sha(text),'raw_definition_sha256':sha(definition(base+name))}
(E/'NMS_NORMALIZATION.json').write_text(json.dumps({'input_sha256':sha(raw),'external_bindings':changes,'opaque_magic':'pure canonical frozen literal [65,83,81,56]','canonical_types':'AdapterRwTypes already selected by coherent RPx_Deployed closure; no duplicated type owners','outputs':outputs,'claim':'Explicit external interpretation/canonical-owner replay, not a raw-template import or a claimed CLOSED row.'},indent=1)+'\n')
