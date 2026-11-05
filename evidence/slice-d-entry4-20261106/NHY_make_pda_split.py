from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;calls=json.loads((E/'NHY_PDA_SOURCE_CALLS.json').read_text());p=E/'NHY_auth.rs.txt';s=p.read_text().split('// NHY split PDA')[0]+'\n// NHY split PDA\n'
s+='''fn NHY_seed_oracle(seeds:&[&[u8]],program:&Pubkey,i:usize,j:usize,k:usize,log:&mut NHY_PdaLog){log.calls+=1;log.seed_count=seeds.len();log.seed_len=seeds[i].len();log.seed_byte=seeds[i][j];log.program_byte=program.as_ref()[k];}
'''
for idx,c in enumerate(calls):
 args=c['args'].strip().rstrip(',');a=args.index('&[')+2;i=a;d=1
 while d:d+=(args[i]=='[')-(args[i]==']');i+=1
 seedtext=args[a:i-1];parts=[];buf='';dep=0
 for ch in seedtext:
  if ch==',' and dep==0:
   if buf.strip():parts.append(buf.strip())
   buf=''
  else:buf+=ch;dep+=(ch in '([')-(ch in ')]')
 if buf.strip():parts.append(buf.strip())
 # Each site has at most one variable key seed plus an independent program.
 if idx in [0,2,4,5,7,8]:
  ctx='let master_account=NHY_KeyView{key:Pubkey::new_from_array(key)};'
 elif idx==1:ctx='let registry_program=Pubkey::new_from_array(key);'
 elif idx==3:ctx='let verifier_key=Pubkey::new_from_array(key);let verifier_program=&verifier_key;'
 else:ctx=''
 program=args[i:].strip().strip(',').strip()
 if program=='&registry_program':ctx+='let registry_program=Pubkey::new_from_array(program_key);'
 elif program=='&loader':ctx+='let loader=Pubkey::new_from_array(program_key);'
 else:ctx+='let pool_key=Pubkey::new_from_array(program_key);let pool_program=&pool_key;'
 ctx+='let registry=NHY_Bumps{bump,programdata_bump};let entry=NHY_Bumps{bump,programdata_bump};let master=NHY_Master{identity:NHY_Identity{asset_mint,bump},bump};let checkpoint=NHY_Checkpoint{bump,checkpoint_sequence};let output_lane=lane_id;let selected_lane=NHY_Lane{bump};'
 expected=[]
 for part in parts:
  t=part.replace('master_account.key().as_ref()','key.as_slice()').replace('registry_program.as_ref()','key.as_slice()').replace('verifier_program.as_ref()','key.as_slice()').replace('Pubkey::new_from_array(master.identity.asset_mint).as_ref()','asset_mint.as_slice()').replace('checkpoint.checkpoint_sequence','checkpoint_sequence').replace('output_lane','lane_id')
  for obj in ['registry','entry','master.identity','master','checkpoint','selected_lane']:t=t.replace(obj+'.programdata_bump','programdata_bump').replace(obj+'.bump','bump')
  expected.append(t)
 for bad in [False,True]:
  n='seed'+str(idx)+('_wrong' if bad else '')
  s+=f'''#[kani::ensures(|r|*r)] #[kani::modifies()]
fn {n}_packet(key:[u8;32],program_key:[u8;32],asset_mint:[u8;32],bump:u8,programdata_bump:u8,checkpoint_sequence:u64,lane_id:u8,i:usize,j:usize,k:usize)->bool{{
 {ctx}
 let expected:&[&[u8]]=&[{','.join(expected)}];kani::assume(i<expected.len());kani::assume(j<expected[i].len());kani::assume(k<32);
 let mut log=NHY_PdaLog{{calls:0,seed_count:0,seed_len:0,seed_byte:0,program_byte:0}};
 NHY_seed_oracle({args},i,j,k,&mut log);
 log.calls=={2 if bad else 1} && log.seed_count==expected.len() && log.seed_len==expected[i].len() && log.seed_len<=32 && expected.len()<=16 && log.seed_byte==expected[i][j] && log.program_byte==program_key[k]
}}
#[kani::proof_for_contract({n}_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn {n}(){{{n}_packet(kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any());}}
'''
for bad in [False,True]:
 n='pda_reply'+('_wrong' if bad else '')
 s+=f'''#[kani::ensures(|r|*r)] #[kani::modifies()]
fn {n}_packet(reply:Result<Pubkey,solana_program::pubkey::PubkeyError>,j:usize)->bool{{
 kani::assume(j<32);let expected=match &reply{{Ok(k)=>Some(k.as_ref()[j]),Err(_)=>None}};
 let result=reply.map_err(|_|ProgramError::InvalidAccountData);
 {'!' if bad else ''}(match (expected,result){{(Some(x),Ok(key))=>x==key.as_ref()[j],(None,Err(ProgramError::InvalidAccountData))=>true,_=>false}})
}}
#[kani::proof_for_contract({n}_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn {n}(){{{n}_packet(NHY_pda_reply(),kani::any());}}
'''
p.write_text(s);x=json.loads((E/'NHY_NATIVE_INPUTS.json').read_text());x['programs/r1-cost-probe/src/NHY_auth.rs']=s;(E/'NHY_NATIVE_INPUTS.json').write_text(json.dumps(x));p=E/'NHY_SOURCE_PINS.json';x=json.loads(p.read_text());x['programs/r1-cost-probe/src/NHY_auth.rs']=hashlib.sha256(s.encode()).hexdigest();p.write_text(json.dumps(x,indent=1)+'\n')
