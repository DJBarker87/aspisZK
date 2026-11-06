from NLK_owned_chain import *
def attempt(a,version,kind,mode):
 version=int(version);entry=kind=='entry';typ='VerifierRegistry'+('Entry' if entry else '')+'V'+str(version)
 fun='decode_verifier_registry_'+('entry_' if entry else '')+'v'+str(version)
 start=FROZEN.index('let '+kind+' = '+fun+'(');end=FROZEN.index(';',start)+1;segment=FROZEN[start:end]
 body=segment.replace(fun+'(', 'oracle(').replace(kind+'_account.data()','account.data()')
 # Explicit complete typed reply; the oracle's local state records only observations.
 body=change_calls(body,'oracle','oracle','&mut log,coordinate,reply')
 size={(1,False):128,(1,True):192,(2,False):256,(2,True):320}[version,entry]
 helper='''use aspis_statement::pool_v1::PoolV1VerifierRegistryFormatError as RF;
fn error()->RF{let i:u8=kani::any();kani::assume(i<12);match i{0=>RF::WrongLength,1=>RF::WrongMagic,2=>RF::WrongVersion,3=>RF::NonZeroReserved,4=>RF::UnsupportedFlags,5=>RF::InvalidStatus,6=>RF::InvalidAuthorityMode,7=>RF::ZeroRequiredBinding,8=>RF::InvalidActivationDelay,9=>RF::InvalidStatementVersion,10=>RF::InvalidRetirementSlot,_=>RF::InvalidDeploymentMode}}
struct Observation{calls:u8,length:usize,byte:u8}
fn oracle(bytes:&[u8],log:&mut Observation,i:usize,reply:Result<TYP,RF>)->Result<TYP,RF>{log.calls+=1;log.length=bytes.len();log.byte=bytes[i];reply}
'''.replace('TYP',typ)
 text=COMMON+helper+ANN+'''fn stage(){
 let data:[u8;SIZE]=kani::any();let coordinate:usize=kani::any();kani::assume(coordinate<SIZE);let expected_byte=data[coordinate];let boxed:Box<[u8]>=Box::new(data);let value=boxed.into_vec();
 let which:u8=kani::any();kani::assume(which<3);let ok:bool=kani::any();let raw=CTOR();let reply=if ok{Ok(raw)}else{Err(error())};
 let account=OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(SIZE),bytes:match which{0=>Ok(value),1=>Err(ProgramError::AccountBorrowFailed),_=>Err(ProgramError::InvalidAccountData)}};
 let mut log=Observation{calls:0,length:0,byte:0};let mut suffix=0u8;
 let out=(||->Result<TYP,ProgramError>{BODY suffix+=1;Ok(KIND)})();CORRUPT
 let expected=if which==1{Err(ProgramError::AccountBorrowFailed)}else if which==2||!ok{Err(ProgramError::InvalidAccountData)}else{Ok(raw)};
 assert!(out==expected&&suffix==if which==0&&ok{1}else{0}&&if which==0{log.calls==1&&log.length==SIZE&&log.byte==expected_byte}else{log.calls==0},"owned234 actual format extent SAME original Vec decoder bytes all12 child errors and exact no-suffix");}
'''.replace('SIZE',str(size)).replace('CTOR',kind+str(version)).replace('TYP',typ).replace('BODY',body).replace('KIND',kind).replace('CORRUPT','if which==0{log.byte^=1;}else{log.calls^=1;}' if mode=='inverse' else '')
 mod='NLK_owned_data'
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(source=P,segment=segment,segment_sha256=sha(segment.encode()),version=version,kind=kind,mode=mode,extent=size,domain='arbitrary full typed child success/all12 errors; stored data success or BorrowFailed/InvalidData; arbitrary original byte coordinate',modifies='local result/log only; input owned account unchanged',limits='four format extents, no independent arbitrary-extent snapshot producer claim; NLA_OwnedData source law is length-parametric'),indent=1)+'\n')
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)))
 return submit(a,'r1_pool_adapter::owned::'+mod+'::stage',P,mod,text,mode)
if __name__=='__main__':
 import sys
 attempt(*sys.argv[1:])
