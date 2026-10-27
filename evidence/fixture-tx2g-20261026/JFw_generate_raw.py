from pathlib import Path
import re,json,sys
from JFw_repair_raw import finish
def emit(path,text):
 p=Path(path)
 if "--check" in sys.argv:assert p.read_text()==text,str(p)
 else:p.write_text(text)

P=2147483647; PP=P*P;MASK=(1<<64)-1
V=json.loads(Path('evidence/fixture-tx2g-20261026/JFw_POWERS.json').read_text())
def fold(x):return (x&P)+(x>>31)
def raw(a,b):
 a,b,c,d,e,f,g,h=a+b
 u=fold((c*g+PP-d*h)&MASK);v=fold((c*h+d*g)&MASK)
 return [(a*e+PP-b*f+2*u+3*P-v)&MASK,(a*f+b*e+u+2*v)&MASK,(a*g+c*e+2*PP-b*h-d*f)&MASK,(a*h+b*g+c*f+d*e)&MASK]
def pack(xs,suf):return 'pack '+' '.join(str(x)+suf for x in xs)
def rec(xs,suf):
 if len(xs)==1:return str(xs[0])+suf
 n=len(xs)//2;return '⟨'+rec(xs[:n],suf)+','+rec(xs[n:],suf)+'⟩'
def state(xs,count):return '⟨⟨'+pack(xs[:4],'#u64')+'⟩,⟨'+pack(xs[4:],'#u64')+'⟩,'+str(count)+'#usize⟩'
txt=Path('lean/JFr_TX2_Tails10.lean').read_text();data=[]
for slot in range(4):
 before=[0]*8
 for kind,k in enumerate([28,26,27]):
  Q=list(map(int,re.findall(r'(\d+)#u32',re.search(rf'def value{kind}_{slot}[^\n]+',txt)[0])))
  raws=[raw(V[k][:4],Q),raw(V[k][4:],Q)]
  after=[x+fold(y) for x,y in zip(before,raws[0]+raws[1])]
  mod=f'JFw_TX2_Raw{slot}{kind}'
  imp='JFw_TX2_FoldPush' if kind==0 else f'JFw_TX2_Raw{slot}{kind-1}'
  s=f'''import {imp}
import JFw_TX2_P28
import JFr_TX2_Tails10
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
'''
  s+=f'def before : FIo_Native.fast_pairing.EbyKDot := {state(before,kind)}\n'
  s+=f'def after : FIo_Native.fast_pairing.EbyKDot := {state(after,kind+1)}\n'
  for half in range(2):
   a=V[k][half*4:half*4+4];b=Q
   s+=f'''def raw{half} : Array U64 4#usize := {pack(raws[half],'#u64')}
theorem pair{half} : FIo_Native.fast_pairing.canonical.Q.raw
    ({pack(a,'#u32')}) ({pack(b,'#u32')})=ok raw{half} := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok]
  rfl
'''
  s+=f'''theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P{k:02}.value
    JFr_TX2_Tails10.value{kind}_{slot}=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    change ¬{kind}#usize≥4096#usize
    decide
  unfold FIo_Native.fast_pairing.EbyKDot.push
  rw [if_neg full]
  change (do let d ← FIo_Native.fast_pairing.canonical.Dot.push before.c0
               ({pack(V[k][:4],'#u32')}) ({pack(Q,'#u32')})
             let d1 ← FIo_Native.fast_pairing.canonical.Dot.push before.c1
               ({pack(V[k][4:],'#u32')}) ({pack(Q,'#u32')})
             ok (.Ok (),⟨d,d1,Usize.wrapping_add before.count 1#usize⟩))=_
  simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,pair1,bind_tc_ok]
  change (do let d ← JFw_TX2_FoldPush.loopCall {{start:=0#usize,«end»:=4#usize}}
               ⟨{pack(before[:4],'#u64')}⟩ raw0
             let d1 ← JFw_TX2_FoldPush.loopCall {{start:=0#usize,«end»:=4#usize}}
               ⟨{pack(before[4:],'#u64')}⟩ raw1
             ok (.Ok (),⟨d,d1,Usize.wrapping_add before.count 1#usize⟩))=_
  simp only [raw0,raw1,JFw_TX2_FoldPush.source,bind_tc_ok]
  rfl
#print axioms pair0
#print axioms pair1
#print axioms source
end AspisR1.{mod}
end
'''
  for half in range(2):
   vals=V[k][half*4:half*4+4]+Q;decls=''
   for j,x in enumerate(vals):
    block=vals[0:4] if j<4 else vals[4:8]
    arr='pack '+' '.join(f'(JFs_TX2_RawMath.extend {a}#u32)' for a in block)
    decls+=f'  have r{j} : Array.index_usize ({arr}) {j%4}#usize=ok (JFs_TX2_RawMath.extend {x}#u32) := rfl\n'
   pattern=rf'(theorem pair{half}.*? := by\n)(.*?)(?=def raw1|theorem source)'
   body=decls+"""  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
"""
   s=re.sub(pattern,lambda m:m[1]+body,s,flags=re.S)
  s=finish(s,dict(slot=slot,kind=kind,k=k,q=Q,before=before,after=after))
  emit(f'lean/{mod}.lean',s)
  data.append(dict(slot=slot,kind=kind,k=k,q=Q,raws=raws,before=before,after=after))
  before=after
emit('evidence/fixture-tx2g-20261026/JFw_RAW.json',json.dumps(data,indent=2)+'\n')
