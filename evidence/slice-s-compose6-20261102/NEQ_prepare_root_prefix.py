from pathlib import Path
import subprocess,sys,json,difflib,hashlib
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','wrong_reply','wrong_statement','wrong_zero']
subprocess.run([sys.executable,str(E/'NEQ_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
old=(E.parent/'slice-s-compose2-20261029/NEE_K052-NEE_oracle.patch').read_text();a=old.index('+fn NEE_digest()');z=old.index('+#[derive',a);construct='\n'.join(l[1:] for l in old[a:z].splitlines() if l.startswith('+')).replace('super::super::PoolV1PairLiveSnapshotV1','PoolV1PairLiveSnapshotV1');errors='\n'.join(l[1:] for l in old.splitlines() if l.startswith('+fn NEE_any_'))
a=f.index('pub enum PoolV1PairForestTerminalFormatErrorV1');z=f.index('\n}',a);variants=[x.strip().strip(',') for x in f[a:z].splitlines()[1:] if x.strip()]
choices=[]
for v in variants:
 if '(' in v:
  name,ty=v[:-1].split('(');v=name+'(NEE_any_'+ty+'())'
 choices.append('PoolV1PairForestTerminalFormatErrorV1::'+v)
any_error='fn any_error()->PoolV1PairForestTerminalFormatErrorV1{match kani::any::<u8>(){'+','.join((str(i) if i<len(choices)-1 else '_')+'=>'+v for i,v in enumerate(choices))+'}}'
body='use super::*;\nuse crate::pool_v1::*;\nuse aspis_core::field::M31;\nuse crate::Digest;\n'+errors+'\n'+construct+'\n'+any_error+'''
struct Frame<'a>{expected:&'a PoolV1PairForestTerminalStatementV1,other:&'a PoolV1PairForestTerminalStatementV1,reply:Result<(),PoolV1PairForestTerminalFormatErrorV1>,called:bool,reached:bool,j:usize,byte:u8}
fn child(s:&PoolV1PairForestTerminalStatementV1,f:&mut Frame)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{assert!(!f.called&&core::ptr::eq(s,f.expected));f.called=true;REPLY}
fn prefix(s:&PoolV1PairForestTerminalStatementV1,f:&mut Frame)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{child(ARG,f)?;let common=s.common();assert!(core::ptr::eq(common,f.expected.common()));let output=[ZEROu8;1880];f.byte=output[f.j];f.reached=true;Ok(())}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn root_prefix(){let s=NEE_statement();let other=NEE_statement();let j:usize=kani::any();kani::assume(j<1880);let mut f=Frame{expected:&s,other:&other,reply:if kani::any(){Ok(())}else{Err(any_error())},called:false,reached:false,j,byte:0};let actual=prefix(&s,&mut f);assert!(actual==f.reply&&f.called&&f.reached==actual.is_ok(),"full validator Result and exact caller continuation");if f.reached{assert!(f.byte==0,"all local output bytes initially zero");}}
'''.replace('REPLY','if f.reply.is_ok(){Err(PoolV1PairForestTerminalFormatErrorV1::WrongMagic)}else{Ok(())}' if mode=='wrong_reply' else 'f.reply').replace('ARG','f.other' if mode=='wrong_statement' else 's').replace('ZERO','1' if mode=='wrong_zero' else '0')
changed=f+'\n#[cfg(kani)]\n#[path="NEQ_root_prefix.rs"]\nmod NEQ_root_prefix;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_root_prefix.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEQ_native_contracts.patch').write_text(patch)
(E/'NEQ_ROOT_PREFIX_CURRENT.json').write_text(json.dumps(dict(mode=mode,all_typed_inputs=True,full_validator_Result=True,initialization='[0u8;1880]',all_observed_indices=True,exact_validator_and_common_places=True,no_external_modifies=True,classification='native rejection/initialization prefix; no protocol loop'),indent=1)+'\n')
