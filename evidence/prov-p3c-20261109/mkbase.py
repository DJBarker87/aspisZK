# builds base_<M>_bridge.lean = P2g PRVEq file (obligation comments stripped) with PRVC_LoopBridge inlined after the options
import re,sys
def mk(src,out):
    s=open(src).read()
    s=re.sub(r'/- PRV-OBLIGATION.*?-/\n\n?','',s,flags=re.S)
    b=open('PRVC_LoopBridge.lean').read().split("open Lean.Order\n",1)[1]
    k="set_option maxRecDepth 2048\n"
    s=s.replace(k,k+"open Lean.Order\n"+b,1)
    open(out,'w').write(s)
if __name__=='__main__': mk(sys.argv[1],sys.argv[2])
