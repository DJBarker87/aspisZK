struct PoolW_Runtime<'a> {
    payer:Pubkey,target:Pubkey,owner:Pubkey,required:u64,initial:u64,
    seeds:[&'a [u8];4],calls:u8,fail:u8,effects:u64,
}
impl PoolW_Runtime<'_> {
    fn record(&mut self,ix:&Instruction,infos:&[AccountInfo<'_>],signed:bool,seeds:&[&[&[u8]]])->ProgramResult {
        let (tag,expect)=if self.initial==0 {(0,system_instruction::create_account(&self.payer,&self.target,self.required,192,&self.owner))}
        else if self.initial<self.required && self.calls==0 {(2,system_instruction::transfer(&self.payer,&self.target,self.required-self.initial))}
        else if self.calls==if self.initial<self.required {1} else {0} {(8,system_instruction::allocate(&self.target,192))}
        else {(1,system_instruction::assign(&self.target,&self.owner))};
        assert!(ix==&expect);assert!(infos.len()==3);
        assert!(infos[0].key==&self.payer && infos[1].key==&self.target && infos[2].key==&system_program::id());
        assert!(signed==(tag!=2));
        if signed {assert!(seeds.len()==1 && seeds[0]==self.seeds);} else {assert!(seeds.is_empty());}
        self.effects=self.effects.wrapping_mul(3).wrapping_add(tag);
        let failed=self.calls==self.fail;self.calls+=1;
        if failed {Err(ProgramError::Custom(0xfeed))} else {Ok(())}
    }
}
impl PoolCpiRuntimeV1 for PoolW_Runtime<'_> {
    fn invoke<'info>(&mut self,ix:&Instruction,infos:&[AccountInfo<'info>])->ProgramResult {self.record(ix,infos,false,&[])}
    fn invoke_signed<'info>(&mut self,ix:&Instruction,infos:&[AccountInfo<'info>],seeds:&[&[&[u8]]])->ProgramResult {self.record(ix,infos,true,seeds)}
}
fn PoolW_call(mode:u8,fail:u8) {
    let owner=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);let payerkey=Pubkey::new_from_array([9;32]);
    let system=system_program::id();let loader=native_loader::id();let rent=Rent::default();let required=rent.minimum_balance(192).max(1);
    let mut target_lamports=match mode {0=>0,1=>1,_=>required};let initial=target_lamports;
    let mut payer_lamports=u64::MAX;let mut system_lamports=1;
    let mut td=[];let mut pd=[];let mut sd=[];
    let target=AccountInfo::new(&key,false,true,&mut target_lamports,&mut td,&system,false,0);
    let payer=AccountInfo::new(&payerkey,true,true,&mut payer_lamports,&mut pd,&system,false,0);
    let sys=AccountInfo::new(&system,false,false,&mut system_lamports,&mut sd,&loader,true,0);
    let master:[u8;32]=kani::any();let sequence:[u8;8]=kani::any();let bump:[u8;1]=kani::any();
    let seeds:[&[u8];4]=[b"aspis-pair-forest-checkpoint-v1",&master,&sequence,&bump];
    let old_effects:u64=kani::any();
    let mut runtime=PoolW_Runtime{payer:payerkey,target:key,owner,required,initial,seeds,calls:0,fail,effects:old_effects};
    let result=create_or_allocate_pda_with_rent(&mut runtime,&payer,&target,&sys,192,&owner,&seeds,&rent);
    let expected_calls=match mode {0=>1,1=>3,_=>2};
    if fail<expected_calls {assert!(result==Err(ProgramError::Custom(0xfeed)));assert!(runtime.calls==fail+1);}
    else {assert!(result==Ok(()));assert!(runtime.calls==expected_calls);}
    let tags:[u64;3]=match mode {0=>[0,0,0],1=>[2,8,1],_=>[8,1,0]};
    let mut expected_effects=old_effects;
    for i in 0..runtime.calls {expected_effects=expected_effects.wrapping_mul(3).wrapping_add(tags[i as usize]);}
    assert!(runtime.effects==expected_effects);
    drop(target);drop(payer);drop(sys);
    // Recording runtime has no account effect: no claim about real System execution.
    assert!(target_lamports==initial && payer_lamports==u64::MAX && system_lamports==1);
}
#[kani::proof]
#[kani::unwind(60)]
fn PoolW_cpi_create_order(){PoolW_call(0,255);}
#[kani::proof]
#[kani::unwind(60)]
fn PoolW_cpi_topup_order(){PoolW_call(1,255);}
#[kani::proof]
#[kani::unwind(60)]
fn PoolW_cpi_funded_order(){PoolW_call(2,255);}
#[kani::proof]
#[kani::unwind(60)]
fn PoolW_cpi_error_prefix(){let mode:u8=kani::any();kani::assume(mode<=2);let fail:u8=kani::any();kani::assume(fail<3);PoolW_call(mode,fail);}
