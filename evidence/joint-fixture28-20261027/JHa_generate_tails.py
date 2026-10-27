from pathlib import Path
import sys
import re
R=Path(__file__).resolve().parents[2];P=2147483647;M=2**64

def nums(s,ty='u32'):return list(map(int,re.findall(r'(\d+)#'+ty,s)))
def coeff(n):return nums((R/f'lean/JFw_TX2_P{n:02}.lean').read_text().split('def value :')[1].split('theorem')[0])
def pack(a,ty='u32'):return '(pack '+' '.join(str(n)+'#'+ty for n in a)+')'
def wide(a):
 a=[str(n)+'#u32' for n in a];return f'⟨⟨⟨{a[0]},{a[1]}⟩,⟨{a[2]},{a[3]}⟩⟩,⟨⟨{a[4]},{a[5]}⟩,⟨{a[6]},{a[7]}⟩⟩⟩'
def state(a,n):return f'⟨⟨{pack(a[:4],"u64")}⟩,⟨{pack(a[4:],"u64")}⟩,{n}#usize⟩'
def raw(x,y):
 a,b,c,d=x;e,f,g,h=y
 u=((c*g+P*P-d*h)%M);u=(u&P)+(u>>31)
 v=(c*h+d*g)%M;v=(v&P)+(v>>31)
 return [(a*e+P*P-b*f+2*u+3*P-v)%M,(a*f+b*e+u+2*v)%M,(a*g+c*e+2*P*P-b*h-d*f)%M,(a*h+b*g+c*f+d*e)%M]
for i in range(10):
 text=(R/f'lean/JGw_Tails{i:02}.lean').read_text();qs={}
 for t in range(3):
  for slot in range(4):
   qs[t,slot]=nums(re.search(rf'def value{t}_{slot} : Q := (.*?)\n',text)[1])
 s=f'''import JFw_TX2_FoldPush
import JFw_TX2_PowerReads
import JFv_TX2_EbyKFinishMeaning
import JFw_TX2_CellUnique
import JGw_Tails{i:02}
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Tails{i}
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
'''
 for slot in range(4):
  st=[0]*8;s+=f'def s{slot}_0 : FIo_Native.fast_pairing.EbyKDot := {state(st,0)}\n'
  for t,n in enumerate([28,26,27]):
   c=coeff(n);q=qs[t,slot];rs=[raw(c[:4],q),raw(c[4:],q)];st=[a+((b&P)+(b>>31)) for a,b in zip(st,rs[0]+rs[1])]
   tag=f'{slot}_{t}';before=f's{slot}_{t}';after=f's{slot}_{t+1}'
   s+=f'def {after} : FIo_Native.fast_pairing.EbyKDot := {state(st,t+1)}\n'
   for k in range(2):
    cp=pack(c[4*k:4*k+4]);qp=pack(q);rp=pack(rs[k],'u64')
    s+=f'''def raw{tag}_{k} : Array U64 4#usize := {rp}
theorem pair{tag}_{k} : FIo_Native.fast_pairing.canonical.Q.raw {cp} {qp}=ok raw{tag}_{k} := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair{tag}_{k}
'''
   s+=f'''theorem push{tag} : FIo_Native.fast_pairing.EbyKDot.push {before} JFw_TX2_P{n:02}.value
    JGw_Tails{i:02}.value{t}_{slot}=ok (.Ok (),{after}) := by
  have full : ¬{before}.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold {before} FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails{i:02}.value{t}_{slot}=
      ok (.Ok {pack(q)}) := by
    apply JFs_TX2_CheckedQ.source
    change ({q[0]}<2147483647 ∧ {q[1]}<2147483647) ∧ ({q[2]}<2147483647 ∧ {q[3]}<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P{n:02}.value=
      ok (Array.make 2#usize [{pack(c[:4])},{pack(c[4:])}]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [{pack(c[:4])},{pack(c[4:])}]) 0#usize=ok {pack(c[:4])} := rfl
  have r1 : Array.index_usize (Array.make 2#usize [{pack(c[:4])},{pack(c[4:])}]) 1#usize=ok {pack(c[4:])} := rfl
'''
   for k in range(2):
    s+=f'''  have d{k} : FIo_Native.fast_pairing.canonical.Dot.push {before}.c{k} {pack(c[4*k:4*k+4])} {pack(q)}=ok {after}.c{k} := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair{tag}_{k},bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {{start:=0#usize,«end»:=4#usize}} {before}.c{k} raw{tag}_{k}=_
    simp only [{before},raw{tag}_{k},JFw_TX2_FoldPush.source]
    rfl
'''
   s+=f'''  simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg full,hw,r0,r1,checked,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,d0,d1]
  have inc : Usize.wrapping_add {before}.count 1#usize={after}.count := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment {before}.count (by unfold {before};decide)
  rw [inc]
#print axioms push{tag}
'''
  vs=[n%P for n in st]
  s+=f'''def value{slot} : FIo_Install.NE := {wide(vs)}
theorem finish{slot} : FIo_Native.fast_pairing.EbyKDot.finish s{slot}_3=ok value{slot} := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s{slot}_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
'''
  for j in range(8):
   s+=f'''  have h{j} := {'va' if j<4 else 'vb'} {j%4}
  change a{j}.val={st[j]}%2147483647 at h{j}
  norm_num at h{j}
  have e{j} : a{j}={vs[j]}#u32 := UScalar.eq_of_val_eq h{j}
'''
  s+='  rw [ea,eb,'+','.join(f'e{j}' for j in range(8))+'] at h\n'
  s+=f'''  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value{slot} := Subtype.ext h
  have same : out=value{slot} := JFw_TX2_CellUnique.source out value{slot} (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish{slot}
theorem source{slot} : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨{i},by decide⟩)
    JFr_TX2_FirstLane.native {slot}#usize=ok value{slot} := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ ({slot}:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok s{slot}_0 from rfl,
'''
  for t in range(3):
   s+=f'''    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨{i},by decide⟩)
      (JFr_TX2_Tails.offset {slot} {t}) (JFr_TX2_Tails.stop {slot} {t})=ok JGw_Tails{i:02}.value{t}_{slot}
      from JGw_Tails{i:02}.source{t}_{slot},
'''
  s+=f'''    push{slot}_0,push{slot}_1,push{slot}_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish{slot}]
#print axioms source{slot}
'''
 s+=f'end AspisR1.JHa_Tails{i}\nend\n'
 dst=R/f'lean/JHa_Tails{i}.lean'
 if '--check' in sys.argv: assert dst.read_text()==s,str(dst)
 else: dst.write_text(s)
