from pathlib import Path
E=Path(__file__).resolve().parent
old=(E.parent/'slice-d-entry6-20261107/NIS_forward.patch').read_text()
s=''.join(l[1:] for l in old.splitlines(True) if l.startswith('+') and not l.startswith('+++'))
a=s.index('fn check<');b=s.index(' let result=',a)
setup=s[a:b].replace('fn check<const PROCESS:bool,const SECOND:bool>(wrong:bool)','fn check<const PROCESS:bool,const SECOND:bool>(wrong:bool)')
variants=['InvalidArgument','InvalidInstructionData','InvalidAccountData','AccountDataTooSmall','InsufficientFunds','IncorrectProgramId','MissingRequiredSignature','AccountAlreadyInitialized','UninitializedAccount','NotEnoughAccountKeys','AccountBorrowFailed','MaxSeedLengthExceeded','InvalidSeeds','AccountNotRentExempt','UnsupportedSysvar','IllegalOwner','MaxAccountsDataAllocationsExceeded','InvalidRealloc','MaxInstructionTraceLengthExceeded','BuiltinProgramsMustConsumeComputeUnits','InvalidAccountOwner','ArithmeticOverflow','Immutable','IncorrectAuthority']
reply='fn reply(p:&Pubkey)->ProgramResult{let k=p.to_bytes();match k[0]%27{0=>Ok(()),1=>Err(ProgramError::Custom(u32::from_le_bytes([k[1],k[2],k[3],k[4]]))),'+''.join(str(i+2)+'=>Err(ProgramError::'+v+'),' for i,v in enumerate(variants))+'_=>Err(ProgramError::BorshIoError(String::from("NIV")))}}\n'
header='use super::*;\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n'+reply+'fn log_child(p:&Pubkey,_:&[AccountInfo<\'_>],_:&[u8])->ProgramResult{reply(p)}\nfn log_wrong_child(p:&Pubkey,a:&[AccountInfo<\'_>],d:&[u8])->ProgramResult{match log_child(p,a,d){Ok(())=>Err(ProgramError::InvalidArgument),Err(_)=>Ok(())}}\nfn forbidden(_: &Pubkey,_:&[AccountInfo<\'_>],_:&[u8])->ProgramResult{assert!(false,"unselected child");Err(ProgramError::InvalidInstructionData)}\n'
body=setup+' let expected=reply(&p);\n let result=if PROCESS{crate::r1_pool_adapter::process(&p,accounts,data)}else{crate::process_r1_cost_probe_instruction(&p,accounts,data)};\n assert!(result==expected,"complete constructor reply forwarded");\n}\n'
tail=s[s.index('#[kani::proof]'):]
t=header+body+tail
p='programs/r1-cost-probe/src/NIV_forward.rs'
(E/'NIV_forward.patch').write_text('--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(t.splitlines()))+' @@\n'+''.join('+'+l for l in t.splitlines(True)))
