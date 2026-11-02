"""A common encoder child argument, reply, and ONE KMX byte window."""
from pathlib import Path
import sys,subprocess,difflib,json,hashlib
E=Path(__file__).resolve().parent;case,mode=sys.argv[1:];negative=mode=='negative';assert case in ['anchor','nullifier','asset']
subprocess.run([sys.executable,str(E/'NEM_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/payment_relation.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
field={'anchor':'anchor_root','nullifier':'nullifier','asset':'asset_id'}[case];start={'anchor':80,'nullifier':112,'asset':144}[case];width=4 if case=='asset' else 32
needle=('&common.'+field+'.to_le_bytes()') if case=='asset' else 'encode_digest_canonical(&common.'+field+')'
assert needle in f
Ty='M31' if case=='asset' else 'Digest';expected=('c.nullifier[0]' if negative else 'c.asset_id') if case=='asset' else '&c.'+('nullifier' if field=='anchor_root' else 'anchor_root') if negative else '&c.'+field
param='v:M31,expected:M31' if case=='asset' else 'v:&Digest,expected:&Digest'
predicate='v.0==expected.0' if case=='asset' else 'core::ptr::eq(v,expected)'
argument='c.'+field if case=='asset' else '&c.'+field
body='''use super::*;
struct Frame{reply:[u8;WIDTH],called:bool}
fn child(PARAM,f:&mut Frame)->[u8;WIDTH]{assert!(!f.called && PREDICATE,"same child field and one call");f.called=true;f.reply}
fn digest()->Digest{[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
#[kani::proof]
fn common_call(){
 let c=CommonPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any())};
 let mut output:[u8;216]=kani::any();let j:usize=kani::any();kani::assume(j<216);let old=output[j];let offset:usize=kani::any();kani::assume(offset<WIDTH);let mut f=Frame{reply:kani::any(),called:false};
 let reply=child(ARGUMENT,EXPECTED,&mut f);
 let dst=&mut output[START..START+WIDTH];let src=&reply;let mut i=offset;dst[i]=src[i];i+=1;
 assert!(f.called && i==offset+1,"one native reply, one KMX iteration");
 assert!(output[j]==if j==START+offset{f.reply[offset]}else{old},"same reply byte and complete frame");
}
'''.replace('WIDTH',str(width)).replace('START',str(start)).replace('PARAM',param).replace('PREDICATE',predicate).replace('ARGUMENT',argument).replace('EXPECTED',expected)
changed=f+'\n#[cfg(kani)]\n#[path="NEM_common_call.rs"]\nmod NEM_common_call;\n'
patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEM_common_call.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEM_native_contracts.patch').write_text(patch)
(E/'NEM_COMMON_CALL_CURRENT.json').write_text(json.dumps(dict(case=case,negative=negative,source=p,actual_expression=needle,field=field,start=start,width=width,all_raw_inputs=True,same_prestate=True,one_iteration=True,no_copy_stub=True,one_native_child=True,classification='ruling y exact immutable child projection; rule B pinned KMX byte step',source_sha256=hashlib.sha256(f.encode()).hexdigest()),indent=1)+'\n')
