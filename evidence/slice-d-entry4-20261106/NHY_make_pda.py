from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;calls=json.loads((E/'NHY_PDA_SOURCE_CALLS.json').read_text());p=E/'NHY_auth.rs.txt';s=p.read_text().split('// NHY PDA cut')[0]+'\n// NHY PDA cut\n'
s+='''struct NHY_KeyView{key:Pubkey} impl NHY_KeyView{fn key(&self)->&Pubkey{&self.key}}
struct NHY_Bumps{bump:u8,programdata_bump:u8}
struct NHY_Identity{asset_mint:[u8;32],bump:u8} struct NHY_Master{identity:NHY_Identity,bump:u8}
struct NHY_Checkpoint{bump:u8,checkpoint_sequence:u64} struct NHY_Lane{bump:u8}
struct NHY_PdaLog{calls:u8,seed_count:usize,seed_len:usize,seed_byte:u8,program_byte:u8}
fn NHY_pda_oracle(seeds:&[&[u8]],program:&Pubkey,reply:Result<Pubkey,solana_program::pubkey::PubkeyError>,i:usize,j:usize,k:usize,log:&mut NHY_PdaLog)->Result<Pubkey,solana_program::pubkey::PubkeyError>{
 log.calls+=1;log.seed_count=seeds.len();log.seed_len=seeds[i].len();log.seed_byte=seeds[i][j];log.program_byte=program.as_ref()[k];reply
}
fn NHY_pda_reply()->Result<Pubkey,solana_program::pubkey::PubkeyError>{use solana_program::pubkey::PubkeyError::*;let tag:u8=kani::any();kani::assume(tag<4);match tag{0=>Ok(Pubkey::new_from_array(kani::any())),1=>Err(MaxSeedLengthExceeded),2=>Err(InvalidSeeds),_=>Err(IllegalOwner)}}
'''
rows=[]
for idx,c in enumerate(calls):
 args=c['args'].strip().rstrip(',');a=args.index('&[')+2;d=1;i=a
 while d:
  d+=(args[i]=='[')-(args[i]==']');i+=1
 seedtext=args[a:i-1];parts=[];buf='';dep=0
 for ch in seedtext:
  if ch==',' and dep==0:
   if buf.strip():parts.append(buf.strip())
   buf=''
  else:
   buf+=ch
   dep+=(ch in '([')-(ch in ')]')
 if buf.strip():parts.append(buf.strip())
 program=args[i:].strip().strip(',').strip();expected_index=[1,2,1,2,1,1,4,4,4][idx]
 common=''' let master_account=NHY_KeyView{key:keys[0]};let registry_program=keys[1];let loader=keys[2];let verifier_program=&keys[3];let pool_program=&keys[4];
 let registry=NHY_Bumps{bump,programdata_bump};let entry=NHY_Bumps{bump,programdata_bump};let master=NHY_Master{identity:NHY_Identity{asset_mint,bump},bump};
 let checkpoint=NHY_Checkpoint{bump,checkpoint_sequence};let output_lane=selected_lane;let selected_lane=NHY_Lane{bump};
'''
 # Expected arguments are constructed separately from the projected scalar/key
 # pre-state, not from a logged output or the oracle's view.
 expected=[];lengths=[]
 for part in parts:
  t=part.replace('master_account.key().as_ref()','keys[0].as_ref()').replace('registry_program.as_ref()','keys[1].as_ref()').replace('verifier_program.as_ref()','keys[3].as_ref()').replace('master.identity.asset_mint','asset_mint').replace('checkpoint.checkpoint_sequence','checkpoint_sequence')
  for obj in ['registry','entry','master.identity','master','checkpoint','selected_lane']:t=t.replace(obj+'.programdata_bump','programdata_bump').replace(obj+'.bump','bump')
  t=t.replace('Pubkey::new_from_array(asset_mint).as_ref()','asset_mint.as_slice()');expected.append(t)
 for bad in [False,True]:
  n=f'pda{idx}'+('_wrong' if bad else '')
  s+=f'''#[kani::ensures(|r|*r)] #[kani::modifies()]
fn {n}_packet(keys:&[Pubkey;5],asset_mint:[u8;32],bump:u8,programdata_bump:u8,checkpoint_sequence:u64,selected_lane:u8,reply:Result<Pubkey,solana_program::pubkey::PubkeyError>,i:usize,j:usize,k:usize)->bool{{
'''+common+f''' let expected:&[&[u8]]=&[{','.join(expected)}];
 kani::assume(i<expected.len());kani::assume(j<expected[i].len());kani::assume(k<32);
 let mut log=NHY_PdaLog{{calls:0,seed_count:0,seed_len:0,seed_byte:0,program_byte:0}};
 let expected_reply=match &reply{{Ok(a)=>Some(a.as_ref()[k]),Err(_)=>None}};
 let result=NHY_pda_oracle({args},reply,i,j,k,&mut log).map_err(|_|ProgramError::InvalidAccountData);
 let reply_ok=match (expected_reply,result){{(Some(a),Ok(b))=>a==b.as_ref()[k],(None,Err(ProgramError::InvalidAccountData))=>true,_=>false}};
 log.calls=={2 if bad else 1} && log.seed_count==expected.len() && log.seed_len==expected[i].len() && log.seed_len<=32 && expected.len()<=16 && log.seed_byte==expected[i][j] && log.program_byte==keys[{expected_index}].as_ref()[k] && reply_ok
}}
#[kani::proof_for_contract({n}_packet)] #[kani::unwind(7)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn {n}(){{let bytes:[[u8;32];5]=kani::any();let keys=bytes.map(Pubkey::new_from_array);{n}_packet(&keys,kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),NHY_pda_reply(),kani::any(),kani::any(),kani::any());}}
'''
 rows.append(dict(index=idx,line=c['line'],argument_source_sha256=hashlib.sha256(args.encode()).hexdigest(),selected_program_key_index=expected_index,seed_count=len(parts),projection='Only accessed key,bump,asset-mint,sequence,lane values retained in local immutable views; exact original source argument text, separate expected slices; no parent or PDA value theorem',domain='All typed projected inputs; every seed <=32, count<=16 proved; arbitrary observed seed/program byte; full SDK PubkeyError carrier'))
p.write_text(s);x=json.loads((E/'NHY_NATIVE_INPUTS.json').read_text());x['programs/r1-cost-probe/src/NHY_auth.rs']=s;(E/'NHY_NATIVE_INPUTS.json').write_text(json.dumps(x));p=E/'NHY_SOURCE_PINS.json';x=json.loads(p.read_text());x['programs/r1-cost-probe/src/NHY_auth.rs']=hashlib.sha256(s.encode()).hexdigest();p.write_text(json.dumps(x,indent=1)+'\n');(E/'NHY_PDA_CUTS.json').write_text(json.dumps(rows,indent=1)+'\n')
