import re,sys
src,dst=sys.argv[1:3];names=sys.argv[3:]
L=open(src).read().split('\n');out=[];n=0
for l in L:
    for nm in names:
        pre='  first | (trace "PRV-S1 PRVEq.AspisR1SelectedMaskProbe.Funs_k1.'+nm+'"; rfl) | '
        if l.startswith(pre):
            l='  first | '+l[len(pre):];n+=1  # keep a one-armed first so layout is unchanged
    out.append(l)
open(dst,'w').write('\n'.join(out));print('rewritten',n,'of',len(names))
