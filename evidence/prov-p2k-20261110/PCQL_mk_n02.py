import re,sys
S='/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/'
p=open(S+'N02P3.lean').read().split('\n')
st=[i for i,l in enumerate(p) if l.startswith('namespace PRVFresh_')][0];en=[i for i,l in enumerate(p) if l.startswith('end PRVFresh_')][0]
fresh=open(S+'e010_dot.lean').read()
out='\n'.join(p[:st+1])+'\n'+fresh+'\n'+'\n'.join(p[en:])
out=out.replace('PRVFresh_RPu_FIq_Native02','PRVFresh_RPu_FIq_Native02_q1').replace('RPu_FIq_Native02_P3','RPu_FIq_Native02_q1')
out=re.sub(r'^-- fresh emission:.*$','-- fresh emission: PCQK_E010 (aspis-core at 4bb3b3f; cargo jobs 4, rustc -Zthreads=1; identity by class receipt PCWE_E003) replaces the P3c fresh block PCQG_aspis_core_field_b3; the two are text-identical modulo the rust_loop attributes. Proof part reused from PRVEq_RPu_FIq_Native02_P3.',out,count=1,flags=re.M)
open('PRVEq_RPu_FIq_Native02_q1.lean','w').write(out)
