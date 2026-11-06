"""Generate only NLM typed source observation interfaces from pinned emission.
These are review inputs; native certificate installation is not inferred.
"""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent
S=Path('docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean').read_text()
header='''import AdapterRwModel
import NJU_Log
set_option autoImplicit false
noncomputable section
namespace NLM_Auth233
open Aeneas Aeneas.Std Result AdapterRw
abbrev Owned := r1_pool_adapter.owned.OwnedAccount
abbrev Key := solana_pubkey.Pubkey
abbrev PE := solana_program_error.ProgramError
abbrev PR := core.result.Result Unit PE
abbrev Master := aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1
abbrev Checkpoint := aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1
abbrev Lane := aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1
abbrev Auth := r1_pool_adapter.AuthenticatedAsq8Accounts
inductive Event where
 | readonlyBuffer (a : Owned) (reply : Result PR)
 | checkpointGuard (a : Owned) (program : Key) (writable : Bool) (reply : Result PR)
 | readonlyAccount (a : Owned) (owner : Key) (reply : Result PR)
 | distinct (accounts : Array Owned 7#usize) (reply : Result PR)
 | data (a : Owned) (reply : Result (core.result.Result (Slice U8) PE))
 | key (a : Owned) (reply : Result Key)
 | toBytes (key : Key) (reply : Result (Array U8 32#usize))
 | fromBytes (bytes : Array U8 32#usize) (reply : Result Key)
 | asRef (key : Key) (reply : Result (Slice U8))
 | decodeMaster (bytes : Slice U8) (reply : Result (core.result.Result Master PE))
 | decodeCheckpoint (bytes : Slice U8) (reply : Result (core.result.Result Checkpoint PE))
 | decodeLane (bytes : Slice U8) (reply : Result (core.result.Result Lane PE))
 | pda (seeds : Slice (Slice U8)) (program : Key) (reply : Result (core.result.Result Key solana_pubkey.PubkeyError))
 | registry (verifierProgram poolProgram : Key) (masterAccount : Owned) (master : Master)
   (registry entry : Owned) (slot : U64) (reply : Result PR)
abbrev Run (A : Type) := NJU_Log.Run Event A
'''
def body(name):
 a=S.index('def r1_pool_adapter.owned.'+name+' ');b=S.index('\n/--',a);return S[a:b]
def instrument(text,events):
 ls=text.splitlines();out=[];i=0;used=[]
 while i<len(ls):
  m=re.match(r'(\s*)let (\w+) ←(.*)',ls[i])
  if not m:i0=i;i+=1;out.append(ls[i0]);continue
  j=i+1
  while j<len(ls) and (len(ls[j])-len(ls[j].lstrip())>len(m[1]) or not ls[j].strip()):j+=1
  expr=' '.join([m[3].strip()]+[z.strip() for z in ls[i+1:j]]).strip()
  event=events.get(m[2])
  if event:
   if event=='DISTINCT':event='.distinct '+expr.split('ops)',1)[1].strip()
   out.append(m[1]+'let '+m[2]+' ← NJU_Log.record ('+event+') ('+expr+')');used.append(dict(binding=m[2],event=event,expression=expr))
  else:out.extend(ls[i:j])
  i=j
 return '\n'.join(out)+'\n',used
m={'r':'.readonlyBuffer proof_account','r1':'.checkpointGuard verifier_checkpoint verifier_program false','r2':'.readonlyAccount master_account pool_program','r3':'.readonlyAccount checkpoint_account pool_program','r4':'.readonlyAccount lane_account pool_program','r5':'DISTINCT','r6':'.data master_account','r7':'.decodeMaster val','p':'.key master_account','a':'.toBytes p','p1':'.fromBytes val1.identity.asset_mint','s':'.asRef p1','r8':'.pda s2 pool_program','r10':'.registry verifier_program pool_program master_account val1 registry_account entry_account current_slot','r11':'.data checkpoint_account','r12':'.decodeCheckpoint val3','a1':'.toBytes p','s3':'.asRef p','r13':'.pda s6 pool_program','p2':'.key checkpoint_account','r15':'.data lane_account','r16':'.decodeLane val6','a3':'.toBytes p','s7':'.asRef p','r17':'.pda s10 pool_program','p3':'.key lane_account','a4':'.toBytes p','a5':'.toBytes p','a6':'.toBytes p2','a7':'.toBytes p3'}
t=body('authenticate_asq8_accounts').replace('def r1_pool_adapter.owned.authenticate_asq8_accounts','def G',1).replace('  Result (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts','  Run (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts',1)
t,used=instrument(t,m)
(E/'NLM_Auth233.lean').write_text(header+t+'\nend NLM_Auth233\n')
(E/'NLM_AUTH233_SITES.json').write_text(json.dumps(dict(emission_sha256=hashlib.sha256(S.encode()).hexdigest(),sites=used),indent=1))

header242="""import NLM_Auth233
set_option autoImplicit false
noncomputable section
namespace NLM_Validate242
open Aeneas Aeneas.Std Result AdapterRw
open NLM_Auth233
abbrev Request := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
abbrev Statement := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Payment := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1
abbrev Candidate := aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
inductive Event where
 | decode (bytes : Slice U8) (reply : Result (core.result.Result Request aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1))
 | poolId (reply : Result (Array U8 32#usize))
 | fromBytes (bytes : Array U8 32#usize) (reply : Result Key)
 | nullifier (payment : Payment) (reply : Result (Array aspis_core.field.M31 8#usize))
 | outputLane (nullifier : Array aspis_core.field.M31 8#usize)
   (reply : Result (core.result.Result U8 aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1))
 | authenticate (program : Key) (accounts : Slice Owned) (pool : Key) (lane : U8) (slot : U64)
   (run : NJU_Log.Run NLM_Auth233.Event (core.result.Result Auth PE))
 | data (account : Owned) (reply : Result (core.result.Result (Slice U8) PE))
 | scan (bytes : Slice U8) (reply : Result (core.result.Result r1_pool_adapter.ScannedAsqaProof PE))
 | reconstruct (request : Request) (auth : Auth) (candidate : Candidate)
   (reply : Result (core.result.Result Statement PE))
abbrev Run (A : Type) := NJU_Log.Run Event A
/-- Nested source occurrence retains the COMPLETE child's chronological Run. -/
def authenticate (ops : Ops) (program : Key) (accounts : Slice Owned)
 (pool : Key) (lane : U8) (slot : U64) : Run (core.result.Result Auth PE) :=
 let child := NLM_Auth233.G ops program accounts pool lane slot
 ⟨child.result,[.authenticate program accounts pool lane slot child]⟩
"""
t=body('validate_asq8').replace('def r1_pool_adapter.owned.validate_asq8','def G',1).replace('  Result (core.result.Result r1_pool_adapter.ValidatedAsqa','  Run (core.result.Result r1_pool_adapter.ValidatedAsqa',1)
m={'r':'.decode instruction_data','a':'.poolId','pool_program':'.fromBytes val.pool_program','a1':'.nullifier val.«public»','r2':'.outputLane a1','r6':'.data val4','r7':'.scan val5','r8':'.reconstruct val val3 val6.candidate_afterstate'}
t,used=instrument(t,m)
t=re.sub(r'\(r1_pool_adapter.owned.authenticate_asq8_accounts ops\)\s+verifier_program accounts pool_program val1 val2','authenticate ops verifier_program accounts pool_program val1 val2',t)
(E/'NLM_Validate242.lean').write_text(header242+t+'\nend NLM_Validate242\n')
(E/'NLM_VALIDATE242_SITES.json').write_text(json.dumps(used,indent=1))
