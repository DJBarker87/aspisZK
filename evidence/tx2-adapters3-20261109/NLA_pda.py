from NLA_registry import *
# Each shape adds the source-ordered address comparison or versioned successor
# to the six predecessor API windows. Never a claim about the PDA value.
def shape(case,field,mode):
 spec=[('expected_registry',0),('registry_programdata',0),('expected_entry',0),('verifier_programdata',0),('expected_registry',1),('expected_entry',1)][case]
 name,occ=spec
 matches=[m.start() for m in re.finditer('let '+name+' = Pubkey::create_program_address',FROZEN)]
 start=matches[occ];end=FROZEN.index(';',start)+1;segment=FROZEN[start:end]
 # Native prestate is complete typed account/registry/entry at the named call.
 setup="""let master_account=OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(0),bytes:Ok(Vec::new())};
 let registry_program=Pubkey::new_from_array(kani::any());let loader=Pubkey::new_from_array(kani::any());let verifier_program=Pubkey::new_from_array(kani::any());
 let registry=REGISTRY();let entry=ENTRY();
 """.replace('REGISTRY','registry2' if case<4 else 'registry1').replace('ENTRY','entry2' if case<4 else 'entry1')
 call=segment.replace('Pubkey::create_program_address(', 'oracle(&mut log,coordinate,reply,')
 # Source comparison sites: programdata replies enter the next policy comparison,
 # while the address sites compare immediately to an input account key.
 text=COMMON+"""
 use solana_program::pubkey::PubkeyError;
 struct Log{count:usize,lens:[usize;5],bytes:[u8;5],program:u8}
 fn oracle(log:&mut Log,i:usize,reply:Result<Pubkey,PubkeyError>,seeds:&[&[u8]],program:&Pubkey)->Result<Pubkey,PubkeyError>{log.count=seeds.len();for n in 0..seeds.len(){log.lens[n]=seeds[n].len();log.bytes[n]=if i<seeds[n].len(){seeds[n][i]}else{0};}log.program=program.to_bytes()[i];reply}
 fn reply()->Result<Pubkey,PubkeyError>{let tag:u8=kani::any();kani::assume(tag<4);match tag{0=>Ok(Pubkey::new_from_array(kani::any())),1=>Err(PubkeyError::MaxSeedLengthExceeded),2=>Err(PubkeyError::InvalidSeeds),_=>Err(PubkeyError::IllegalOwner)}}
 """+ANN+'fn stage(){'+setup+"""
 let coordinate:usize=kani::any();let slot:usize=kani::any();kani::assume(coordinate<32&&slot<5);
 let reply=reply();let expected_key=Pubkey::new_from_array(kani::any());let returned=reply.clone();let mut suffix=0u8;
 let mut log=Log{count:0,lens:[0;5],bytes:[0;5],program:0};
 let mut result=(||->ProgramResult{SEGMENT if NAME!=expected_key{return Err(ProgramError::InvalidAccountData);}suffix+=1;Ok(())})();CORRUPT
 let expected=returned.map_err(|_|ProgramError::InvalidAccountData).and_then(|p|if p==expected_key{Ok(())}else{Err(ProgramError::InvalidAccountData)});
 let good=PROPERTY;
 assert!(good,"PDA same-call seeds reply comparison and error prefix");}
 """.replace('SEGMENT',call).replace('NAME',name)
 # Exact seed expressions and program id taken from the source call itself.
 content=segment[segment.index('(')+1:segment.rindex(')')].strip()
 # Format contains trailing comma after &program; parse last comma-terminated arg.
 split=content.rsplit('\n',1);program=split[-1].strip().rstrip(',');seeds=split[0].rstrip().rstrip(',')
 expected_seeds='let seeds:&[&[u8]]='+seeds+';'
 props=['result==expected&&suffix==if expected.is_ok(){1}else{0}', '{'+expected_seeds+'let size=if slot<seeds.len(){seeds[slot].len()}else{0};let byte=if slot<seeds.len()&&coordinate<size{seeds[slot][coordinate]}else{0};log.count==seeds.len()&&log.lens[slot]==size&&log.bytes[slot]==byte&&log.program==('+program+').to_bytes()[coordinate]}']
 corrupt=['result=if result.is_ok(){Err(ProgramError::InvalidAccountData)}else{Ok(())};','log.program^=1;']
 return text.replace('PROPERTY',props[field]).replace('CORRUPT',corrupt[field] if mode=='inverse' else ''),segment

def attempt(a,case,field,mode):
 text,segment=shape(case,field,mode);mod='NLA_pda'
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+line for line in text.splitlines(True)))
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(source=P,segment=segment,segment_sha256=sha(segment.encode()),case=case,field=field,mode=mode,domain='arbitrary typed pre-state, complete four-arm API reply; byte<32,slot<5; op38 VALUE unconstrained',missing='deployed SDK ABI producer and source-ordered policy successor instantiation; programdata comparison here is a generic continuation support'),indent=1)+'\n')
 return submit(a,'r1_pool_adapter::owned::'+mod+'::stage',P,mod,text,mode)
