"""Check local-context native-step migration preserves original instrumented body."""
from NEK_scan import *
import re
out=[]
for a,num in [('NEK_K001',50),('NEK_K003',52)]:
 s=ROOT/f'evidence/native-front2-20261028/NDE_K{num:03}/sources/NDE_src'
 o=read_json(E/(a+'_overlay.json'));p='crates/aspis-statement/src/state_only_poseidon.rs';old=(s/p).read_text();new=o[p]
 names=re.findall(r'static mut (\w+):',(s/'crates/aspis-statement/src/NDE_poseidon.rs').read_text())
 back=new
 for name in names:back=back.replace('ctx.'+name,'NDE_native::'+name)
 back=back.replace(', ctx:&mut NDE_native::NEK_Context','').replace(', &mut NDE_native::NEK_Context','').replace('input,&mut NDE_native::NEK_Context::new()','input').replace('crate::NEK_kmx','crate::NDE_kmx')
 assert back==old,a
 h=o['crates/aspis-statement/src/NDE_poseidon.rs'];oh=(s/'crates/aspis-statement/src/NDE_poseidon.rs').read_text()
 assert not re.search(r'\bstatic\s+mut\b',h)
 # All original log reads/writes survive one-for-one, with the same field names.
 counts={name:dict(old=len(re.findall(r'\b'+name+r'\b',oh))-1,new=len(re.findall(r'ctx\.'+name+r'\b',h))) for name in names}
 assert all(v['old']==v['new'] for v in counts.values()),counts
 out.append(dict(attempt=a,original=f'NDE_K{num:03}',native_body_inverse_projection_equal=True,original_sha256=sha(old.encode()),migrated_sha256=sha(new.encode()),log_reference_counts=counts,context='owned local record, unique &mut parameter',scope='exact historical instrumented step; native/model induction and tool semantic transport retained'))
(E/'NEK_LOCAL_CONTEXT_ASSOCIATION.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(out),'native-step inverse projections and complete log reference counts')
