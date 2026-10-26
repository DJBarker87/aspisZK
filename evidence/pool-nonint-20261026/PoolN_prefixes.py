"""Copy literal native handler prefixes, ending after the rejecting guard.
The emitted prefix body is a contiguous original source span, not a rewritten
metadata predicate. Complete source signatures and offsets are pinned below.
No production source is edited. The suffix is replaced only by Ok(()) in the
new test-only copy; error propagation in the copied prefix is unchanged.
"""
from pathlib import Path
import hashlib,json
B=Path(__file__).parent
specs=[
 ('ASDI','processor','process_deposit_with_runtime_v1','let state = load_canonical_pool_state(program_id, pool)?;',1,80),
 ('ASPT','processor','process_private_transfer_with_runtime_v1','let state = load_canonical_pool_state(program_id, pool)?;',1,'crate::instruction::POOL_V1_SPEND_INSTRUCTION_BYTES'),
 ('ASWD','processor','process_withdrawal_with_runtime_v1','let state = load_canonical_pool_state(program_id, pool)?;',1,'crate::instruction::POOL_V1_SPEND_INSTRUCTION_BYTES'),
 ('ASPP','processor','process_prepare_settlement_with_runtime_v1','let state = CanonicalPoolStateV1::decode_account_from_program_invariant(program_id, pool)?;',2,'crate::prepared_settlement_instruction::POOL_V1_PREPARE_SETTLEMENT_INSTRUCTION_BYTES'),
 ('ASPF','processor','process_settle_prepared_with_runtime_v1','let state = load_canonical_pool_state(program_id, pool)?;',2,'crate::settle_prepared_instruction::POOL_V1_SETTLE_PREPARED_INSTRUCTION_BYTES'),
 ('ASIN','processor','process_initialize_with_runtime_v1','require_payer_and_system_program(payer, system_program_account)?;',7,'crate::instruction::POOL_V1_INITIALIZE_INSTRUCTION_BYTES'),
 ('AS8I','pair_forest','process_pair_forest_initialize_with_runtime_v1','require_payer_and_system_program(payer, system_program_account)?;',14,'crate::instruction::POOL_V1_INITIALIZE_INSTRUCTION_BYTES'),
 ('AS8D','pair_forest','process_pair_forest_deposit_with_runtime_v1','let master = decode_terminal_master_box_v1(program_id, master_account)?;',3,80),
 ('ASQ8','pair_forest','process_pair_forest_terminal_with_verifier_v1','let master = decode_terminal_master_box_v1(program_id, master_account)?;',3,324),
]
outputs={m:'\n#[cfg(kani)]\nmod PoolN_prefixes {\nuse super::*;\n'+(B/'PoolN_fixture.rs').read_text() for m in ['processor','pair_forest']}
manifest=[]
for tag,module,name,end,count,insize in specs:
 path=Path(f'programs/aspis-pool/src/{module}.rs');src=path.read_text();pos=src.index('fn '+name+'<');start=src.index('\n{',pos)+2 if '\nwhere\n' in src[pos:src.index(end,pos)] else src.index('{\n',pos)+1
 # Generic bounds may contain function arrows but no opening brace except body.
 stop=src.index(end,start)+len(end)
 body=src[start:stop]
 assert not body.lstrip().startswith('use ') and body.count('let ')>0
 outputs[module]+=f'\nfn PoolN_{tag}_prefix(program_id: &Pubkey, accounts: &[AccountInfo<\'_>], instruction_data: &[u8]) -> ProgramResult {{'+body+'\nOk(())\n}\n'
 fixture={'ASIN':0,'ASPT':1,'ASWD':2,'ASPP':3,'ASPF':4,'AS8I':5,'ASDI':6,'AS8D':7,'ASQ8':8}[tag]
 for n in [192,1768]:
  role=0
  if tag in ['ASPP','ASPF']:role=1
  if tag=='AS8I':role=12
  # All other accounts have distinct identities and no initialized bytes.
  # Their contents are not read before the CP guard on these prefix paths.
  harness=f'''
#[kani::proof]
#[kani::unwind({max(n+4, count+4)})]
fn PoolN_{tag}_prefix_fixedmeta_{n}() {{
 let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let cpkey=Pubkey::new_from_array([8;32]);
 let mut bytes:[u8;{n}]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
 let cp=AccountInfo::new(&cpkey,false,{str(tag not in ["AS8D","ASQ8"]).lower()},&mut balance,&mut bytes,{"&id" if n==192 else "&foreign"},false,0);
 let keys:[Pubkey;{count}]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
 let mut balances=[0u64;{count}];let mut dummy=[[0u8;0];{count}];
 let mut accounts=Vec::new();
 for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {{
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
 }}
 accounts[{role}]=cp.clone();
 let instruction=PoolN_fixture({fixture});
 let result=PoolN_{tag}_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(PoolV1ProgramError::InvalidPayer.into()),"payer rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}}
'''
  # Cover only the reachable rejecting gate. Metadata choices can reject earlier;
  # there must also be one witness that reaches length/type or owner rejection.
  if tag not in ['ASIN','AS8I']:
   err='PoolV1ProgramError::InvalidAccountType.into()' if n==192 else 'ProgramError::IncorrectProgramId'
   harness=harness.replace('PoolV1ProgramError::InvalidPayer.into()',err).replace('payer rejection reached','type/owner rejection reached')
  outputs[module]+=harness
 manifest.append(dict(handler=tag,file=str(path),source_sha256=hashlib.sha256(src.encode()).hexdigest(),function=name,start_byte=start,end_byte=stop,start_line=src[:start].count('\n')+1,end_line=src[:stop].count('\n')+1,body_sha256=hashlib.sha256(body.encode()).hexdigest(),scope=f'Checkpoint substituted at slot{role}; fixed canonical fixture of instruction length {insize}; no suffix/frame claim for other roles; first-byte frame only in these prefix probes'))
for module,s in outputs.items():(B/f'PoolN_{module}_prefixes.rs').write_text(s+'\n}\n')
(B/'PoolN_prefix-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
