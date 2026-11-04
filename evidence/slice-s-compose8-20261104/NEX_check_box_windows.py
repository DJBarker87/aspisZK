"""Support-only audit of exact safe Box source windows, with no row promotion."""
from pathlib import Path
import sys,json,difflib,hashlib
import NEX_validate as v
E=v.E
sys.path.insert(0,str(E.parent/'slice-s-compose7-20261103'))
from NEU_bridge_checks import COMMON
FUNCTIONS={'common':'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_terminal_common_boxed_v1','lane':'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_lane_transition_boxed_v1','afterstate':'crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pair_afterstate_boxed_v1','snapshot':'crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pair_live_snapshot_boxed_v1'}
def erased(m):
 text=m['native'];name=m['function'].rsplit('::',1)[1]
 text=text.replace('fn native(','fn '+name+'(').replace('    bytes: &[u8], f: &mut Frame,','    bytes: &[u8],')
 if m['family']=='common':
  text=text.replace('digest(','decode_digest_canonical(').replace('    f)','    )')
  text=text.replace('lane(&bytes[LATE_STATEMENT_OFFSET..PAYMENT_STATEMENT_OFFSET],f)','decode_lane_transition_boxed_v1(&bytes[LATE_STATEMENT_OFFSET..PAYMENT_STATEMENT_OFFSET])')
 else:
  child={'lane':'decode_pool_v1_pair_late_public_statement_boxed_v1','afterstate':'decode_pool_v1_pair_verified_afterstate_v1','snapshot':'decode_pool_v1_pair_live_snapshot_v1'}[m['family']]
  text=text.replace('child(bytes,f)',child+'(bytes)')
 text=text.replace('let boxed=Box::new(','Ok(Box::new(').replace('    });\n    f.allocated=&*boxed;\n    Ok(boxed)','    }))').replace('    );\n    f.allocated=&*boxed;\n    Ok(boxed)','    ))')
 return text

def attempt(a,family,mode):
 m=v.read(E/(a+'-shape.json'));assert m['family']==family and m['mode']==mode and m['function']==FUNCTIONS[family]
 snapshot=v.native(a,mode=='positive');path=m['function'].split('::')[0];f=v.inherited.frozen_source(m['function']);name=m['function'].rsplit('::',1)[1];start=f.index('fn '+name+'(');end=f.index('\n}',start)+2
 assert m['frozen_body']==f[start:end]
 if mode in ['positive','value']:assert erased(m)==m['frozen_body']
 hook=f+'\n#[cfg(kani)]\n#[path="NEX_decoder.rs"]\nmod NEX_decoder;\n'
 patch=''.join(difflib.unified_diff(f.splitlines(True),hook.splitlines(True),fromfile='a/'+path,tofile='b/'+path))+'--- /dev/null\n+++ b/'+path.rsplit('/',1)[0]+'/NEX_decoder.rs\n@@ -0,0 +1,'+str(len(m['source'].splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in m['source'].splitlines())
 assert snapshot['NEX_native_contracts.patch']==patch
 assert 'assert!(core::ptr::eq(&*out,f.allocated));' in m['source']
 assert 'assert!(!core::ptr::eq((&*out) as *const _ as *const u8,bytes.as_ptr()));' in m['source']
 return m

def common():
 pairs=[['NEX_K003','NEX_K004']]+[[f'NEX_K{8+2*i:03}',f'NEX_K{9+2*i:03}'] for i in range(14)]
 for slot,pair in enumerate(pairs):
  for a,mode in zip(pair,['positive','value']):
   m=attempt(a,'common',mode);assert m['selected']==slot and len(m['fields'])==15
 for a,mode in [('NEX_K005','allocation'),('NEX_K006','argument'),('NEX_K007','reply')]:attempt(a,'common',mode)
 return dict(function=FUNCTIONS['common'],fields=15,native_pairs=pairs,allocation_control='NEX_K005',argument_control='NEX_K006',reply_control='NEX_K007',source_erasure=True,ruling_aa=True,composed_status='OPEN',exact_remaining_obligation='closed native lane child plus reached-child model/domain substitution; this packet audits supporting windows only')
if __name__=='__main__':
 out=common();(E/'NEX_COMMON_CHECKED.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
