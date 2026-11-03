from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','negative']
subprocess.run([sys.executable,str(E/'NEQ_prepare_root_prefix.py'),'positive'],check=True)
p=E/'NEQ_native_contracts.patch';s=p.read_text();head,rest=s.split('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_root_prefix.rs\n',1);body=''.join(l[1:]+'\n' for l in rest.splitlines()[1:] if l.startswith('+'))
body+='''
fn finish(mut output:[u8;1880])->Result<[u8;1880],PoolV1PairForestTerminalFormatErrorV1>{CORRUPTOk(output)}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn root_return(){let output:[u8;1880]=kani::any();let j:usize=kani::any();kani::assume(j<1880);let old=output[j];match finish(output){Ok(bytes)=>assert!(bytes[j]==old,"complete typed root returned output"),Err(_)=>assert!(false)}}
'''.replace('CORRUPT','output[0]^=1;' if mode=='negative' else '')
p.write_text(head+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_root_prefix.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines()))
(E/'NEQ_ROOT_RETURN_CURRENT.json').write_text(json.dumps(dict(mode=mode,full_typed_Result=True,all_1880_indices=True,classification='return ownership and complete output bytes, no protocol loop; KMX copied carrier controls'),indent=1)+'\n')
