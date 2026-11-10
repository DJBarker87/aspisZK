import re
S='/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/'
t=open(S+'k3.lean').read()
st=t.index('namespace PRVFresh_');st=t.index('\n',st)+1;en=t.index('end PRVFresh_')
fresh=open(S+'e010_mask.lean').read().replace('end PCQK_core\n','').replace('end PCQK_core','')
out=t[:st]+fresh+'\n'+t[en:]
out=out.replace('Funs_k3','Funs_q1')
out=re.sub(r'^-- fresh emission:.*$','-- fresh emission: PCQK_E010 (aspis-core at 4bb3b3f; cargo jobs 4, rustc -Zthreads=1; identity by class receipt PCWE_E003) replaces the P1k fresh block PCVR_core; the 46 blocks are text-identical modulo rust_loop attributes (PCQL_mk_mask.py). Proof part reused from PRVEq_AspisR1SelectedMaskProbe_Funs_k3.',out,count=1,flags=re.M)
open('PRVEq_AspisR1SelectedMaskProbe_Funs_q1.lean','w').write(out)
