from pathlib import Path
import subprocess,sys,json,difflib
E=Path(__file__).resolve().parent;case,mode=sys.argv[1:];assert case in ['borrow_length','request_prefix'] and mode in ['positive','negative']
subprocess.run([sys.executable,str(E/'NEQ_prepare_root_window.py'),'9','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
if case=='borrow_length':
 body='''use super::*;
#[kani::proof]
fn final_native(){let backing=[();1];let length:usize=kani::any();
 // Unit has size zero: every usize length covers zero bytes, so the live,
 // aligned, nonnull backing pointer supplies a valid borrowed Unit slice.
 let slice=unsafe{core::slice::from_raw_parts(backing.as_ptr(),length)};
 let actual:Result<&[();216],core::array::TryFromSliceError>=slice.try_into();
 assert!(actual.is_ok()==(length==WIDTH),"all-usize native borrowed conversion length guard");
 // Zero-sized pointer identity is not claimed: K117 refuted that extra assertion.
}
'''.replace('WIDTH','217' if mode=='negative' else '216')
else:
 body='''use super::*;
fn prefix(length:usize,bytes:&[u8;8])->Result<PoolV1TransitionKind,PoolV1PairForestTerminalFormatErrorV1>{if length!=POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES{return Err(PoolV1PairForestTerminalFormatErrorV1::WrongLength)}if bytes[..4]!=POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC{return Err(PoolV1PairForestTerminalFormatErrorV1::WrongMagic)}if bytes[4]!=POOL_V1_PAIR_FOREST_TERMINAL_VERSION{return Err(PoolV1PairForestTerminalFormatErrorV1::WrongVersion)}let kind=transition_kind(bytes[@KIND_BYTE@])?;if bytes[6]!=POOL_V1_DIGEST_ENCODING_VERSION{return Err(PoolV1PairForestTerminalFormatErrorV1::WrongDigestEncoding)}if bytes[7]!=0{return Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding)}Ok(kind)}
fn reference(length:usize,b:&[u8;8])->Result<PoolV1TransitionKind,PoolV1PairForestTerminalFormatErrorV1>{if length!=320{return Err(PoolV1PairForestTerminalFormatErrorV1::WrongLength)}if b[0]!=POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC[0]||b[1]!=POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC[1]||b[2]!=POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC[2]||b[3]!=POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC[3]{return Err(PoolV1PairForestTerminalFormatErrorV1::WrongMagic)}if b[4]!=POOL_V1_PAIR_FOREST_TERMINAL_VERSION{return Err(PoolV1PairForestTerminalFormatErrorV1::WrongVersion)}let kind=match b[5]{1=>PoolV1TransitionKind::PrivateTransfer,2=>PoolV1TransitionKind::Withdrawal,_=>return Err(PoolV1PairForestTerminalFormatErrorV1::InvalidTransitionKind)};if b[6]!=POOL_V1_DIGEST_ENCODING_VERSION{return Err(PoolV1PairForestTerminalFormatErrorV1::WrongDigestEncoding)}if b[7]!=0{return Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding)}Ok(kind)}
#[kani::proof]
fn final_native(){let bytes:[u8;8]=kani::any();let length:usize=kani::any();assert!(prefix(length,&bytes)==reference(length,&bytes),"native request prefix, all lengths and header bytes, exact parser input and error priority");}
'''.replace('@KIND_BYTE@','6' if mode=='negative' else '5')
changed=f+'\n#[cfg(kani)]\n#[path="NEQ_final_native.rs"]\nmod NEQ_final_native;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_final_native.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEQ_native_contracts.patch').write_text(patch)
(E/'NEQ_FINAL_NATIVE_CURRENT.json').write_text(json.dumps(dict(case=case,mode=mode,all_usize_lengths=True,classification='native generic borrowed length guard ONLY with valid zero-sized backing; no ZST pointer identity; or request-prefix scalar cut; no whole decoder/root credit by itself',new_shape='zero-byte physical backing permits every usize length; typed nonzero-byte matched-length carriers checked separately' if case=='borrow_length' else 'root length metadata and unchanged first8 bytes; same actual parser byte5'),indent=1)+'\n')
