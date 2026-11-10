# builds base_<M>_bridge.lean = P2g PRVEq file (obligation comments stripped) with PRVC_LoopBridge inlined after the options.
# PCVD change: UNDROP restores named PRV-FRESH-DROPPED fresh declarations; SHIMS inserts constant-binding definitions
# (the cross-crate fresh emission types a constant as `Result T`; the shim reads it as `ok <gate constant>`).
import re,sys
UNDROP=set()   # def names (as in the file) whose dropped block is restored verbatim
SHIMS=[]       # lines inserted right after `namespace PRVFresh_*`
SLICE=None     # optional: set of def names to keep from the fresh namespace (None = keep all)
def mk(src,out):
    s=open(src).read()
    s=re.sub(r'/- PRV-OBLIGATION.*?-/\n\n?','',s,flags=re.S)
    dropped=[]
    def rep(m):
        t=m.group(1)
        d=re.search(r'(?:^|\n)def\s+(\S+)',t)
        nm=d.group(1) if d else None
        if nm in UNDROP: return t+'\n\n'
        dropped.append(t); return ''
    s=re.sub(r'/- PRV-FRESH-DROPPED[^\n]*\n(.*?)\n-/\n\n?',rep,s,flags=re.S)
    open(out+'.dropped','w').write('\n=====\n'.join(dropped))
    if SHIMS:
        s=re.sub(r'(namespace PRVFresh_\w+\n)',lambda m:m.group(1)+'\n'+'\n'.join(SHIMS)+'\n\n',s,count=1)
    b=open('PRVC_LoopBridge.lean').read().split("open Lean.Order\n",1)[1]
    k="set_option maxRecDepth 2048\n"
    s=s.replace(k,k+"open Lean.Order\n"+b,1)
    open(out,'w').write(s)
if __name__=='__main__': mk(sys.argv[1],sys.argv[2])
