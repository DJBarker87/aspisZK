#!/usr/bin/env python3
"""PCWN: build PRVEq_PB_w3.lean from PRVEq_PB_w2.lean (P4x). Removes the abbrev shim; adds the new-library constants copied verbatim
(attributes omitted) in namespace PCWN_NewLib, qualifies the two names in the fresh text, and proves fresh = gate by transport."""
import re,sys
s=open('../prov-p4x-20261110/PRVEq_PB_w2.lean').read()
# 1. drop shim
a=s.index('namespace Aeneas.Std\n/-- PCWH library-version shim');b=s.index('end Aeneas.Std\n',a)+len('end Aeneas.Std\n')
s=s[:a]+'@@NEWLIB@@\n'+s[b:]
newlib=open(sys.argv[1]).read()
s=s.replace('@@NEWLIB@@',newlib)
# 2. qualify the two names inside the fresh namespace only
i=s.index('namespace AspisR1PublicPreparation\nnamespace PRVFresh');j=s.index('end PRVFresh_AspisR1PublicPreparation_Funs_w1')
mid=s[i:j]
mid=re.sub(r'(?<![\w.])core\.result\.Result\.Insts\.CoreOpsTry\.branch',lambda m:'PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch',mid)
mid=re.sub(r'(?<![\w.])core\.result\.Result\.Insts\.CoreOpsTry_traitFromResidualResult\.from_residual',lambda m:'PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual',mid)
s=s[:i]+mid+s[j:]
# 3. theorem proofs for the two functions using branch
for nm in ['frontier','public_bytes']:
    pat=re.compile(r'(theorem PRVEq\.AspisR1PublicPreparation\.Funs_w1\.pool_v1\.pair_forest_semantic_terminal\.r0\.Public\.public_bytes'+('\\.frontier' if nm=='frontier' else '')+r' : [^\n]*\n)  first \| (\(trace "PRV-S1[^\n]*?rfl\)) \| (\(trace "PRV-S2 [^\n]*?)try rfl; done\)\n')
    m=pat.search(s); assert m,nm
    s=s[:m.start()]+m.group(1)+'  first | '+m.group(2)+' | '+m.group(3)+'pb_chain; done)\n'+s[m.end():]
open(sys.argv[2],'w').write(s)
