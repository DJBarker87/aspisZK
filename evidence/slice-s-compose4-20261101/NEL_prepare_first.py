from pathlib import Path
import sys,subprocess,difflib,json,hashlib
E=Path(__file__).resolve().parent;negative=sys.argv[1]=='negative'
subprocess.run([sys.executable,str(E/'NEL_prepare_window.py'),'1','positive'],check=True)
path='crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs';frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
a=frozen.index('fn first_canonical_byte(');z=frozen.index('\n}',a)+2;original=frozen[a:z];assert 'encode_digest_canonical(digest)[0]' in original
body='''#![allow(non_snake_case)]
use super::*;
use aspis_core::field::M31;
struct Frame{expected:Digest,reply:[u8;32],called:bool}
fn encode(d:&Digest,f:&mut Frame)->[u8;32]{let k:usize=kani::any();kani::assume(k<8);assert!(d[k].0==f.expected[k].0&&!f.called,"same first-byte digest argument");f.called=true;f.reply}
#[kani::requires(!f.called && *d==f.expected)]
#[kani::modifies(&mut f.called)]
#[kani::ensures(|r| *r==f.reply[0] && f.called)]
fn threaded_first(d:&Digest,f:&mut Frame)->u8{encode(d,f)[0]}
#[kani::proof_for_contract(threaded_first)]
fn first(){let d=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];let mut f=Frame{expected:d,reply:kani::any(),called:false};let _=threaded_first(&d,&mut f);}
'''
if negative:body=body.replace('*r==f.reply[0]','*r==(f.reply[0]^1)')
changed=frozen+'\n#[cfg(kani)]\n#[path="NEL_first.rs"]\nmod NEL_first;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEL_first.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEL_native_contracts.patch').write_text(patch)
(E/'NEL_FIRST_CURRENT.json').write_text(json.dumps(dict(negative=negative,source=path,frozen_body_sha256=hashlib.sha256(original.encode()).hexdigest(),exact_expression_projection=True,all_raw_inputs=True,callee_domain='all typed raw Digest; no canonicality precondition added',full_result=True,empty_external_modifies=True,local_ordered_log=True,arbitrary_full_reply=True),indent=1)+'\n')
