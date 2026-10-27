from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];P=R/'evidence/fixture-tx2o-20261027/JGq_UNCHECKED';out={}
for tag in ['Data','Powers0','Powers1','Terms0','Terms1','Scale0','Scale1']:
 s=(P/f'JGq_Libra{tag}.lean.txt').read_text().replace('JGq_Libra','JGs_Libra');out['JGs_Libra'+tag]=s
x={'__file__':str(R/'evidence/fixture-tx2p-20261027/JGs_preflight.py')};exec((R/'evidence/fixture-tx2p-20261027/JGs_preflight.py').read_text().split('for j in range(4):parts')[0],x)
w=x['x']['wide'];mul=x['mul'];add=x['add'];qp=x['qp'];scale=x['scale'];quarter=x['quarter'];alpha=x['alpha'];aps=x['aps'];sf=x['sf'];qmul=x['qmul'];zero=x['zero'];perm=x['perm']
def head(imports,ns):return '\n'.join('import '+v for v in imports)+f'\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.{ns}\nopen Aeneas Aeneas.Std Result ControlFlow\n'
def end(ns):return f'end AspisR1.{ns}\nend\n'
ns='JGs_LibraEnd';s=head(['JGs_LibraScale0','JGs_LibraScale1','JGs_LibraTerms0','JGs_LibraTerms1'],ns)
operations=[];v=[zero[:] for _ in range(4)]
for side in [0,1]:
 q=alpha[32+4*side:36+4*side];lo=sf(sum([qp(q,j) for j in range(4)],[]),aps[0]);terms=[scale(mul(aps[1][perm[j]],qp(q,4*j)+[0]*4),quarter) for j in range(4)];first2=add(*terms[:2]);first3=add(first2,terms[2]);allv=add(first3,terms[3]);sn=f'JGs_LibraScale{side}.value'
 def op(name,func,a,b,val):
  operations.append((name,func,a,b,val));return name
 if side==0:
  v0=mul(lo,allv);op('a','mul',sn,'JGs_Libra.sum0_4',v0)
  b=mul(lo,first3);op('b','mul',sn,'JGs_Libra.sum0_3',b)
  c=mul(b,qp(q,16)+[0]*4);op('c','mul_qm31','b','JGs_Libra.q0_16',c)
  v[0]=v0;v[1]=c
  middle=v[:]
 else:
  d=scale(aps[1][perm[3]],quarter);op('d','mul_m31','JGq_Powers1.p1','FIo_Native.weights.QUARTER',d)
  e=mul(lo,d);op('e','mul',sn,'d',e)
  f=add(v[1],e);op('f','add','c','e',f)
  g=mul(lo,allv);op('g','mul',sn,'JGs_Libra.sum1_4',g)
  h=mul(g,qp(q,4)+[0]*4);op('h','mul_qm31','g','JGs_Libra.q1_4',h)
  i=mul(lo,first2);op('i','mul',sn,'JGs_Libra.sum1_2',i)
  j=mul(i,qp(q,20)+[0]*4);op('j','mul_qm31','i','JGs_Libra.q1_20',j)
  v[1]=f;v[2]=h;v[3]=j
for name,func,a,b,val in operations:
 s+=f'def {name} : FIo_Install.NE := {w(val)}\ntheorem call_{name} : FIo_Native.aspis_core.field.wide_exact.WideExact.{func} {a} {b}=ok {name} := by with_unfolding_all rfl\n#print axioms call_{name}\n'
s+='def initial : Array FIo_Install.NE 4#usize := Array.repeat 4#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO\n'
s+='def middle : Array FIo_Install.NE 4#usize := Array.make 4#usize [a,c,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]\n'
s+='def value : Array FIo_Install.NE 4#usize := Array.make 4#usize [a,f,h,j]\n'+end(ns);out[ns]=s
for side in [0,1]:
 ns='JGs_LibraNative';s=head([f'JGs_LibraPowers{side}',f'JGs_LibraTerms{side}','JGs_LibraWrites'],ns)
 before='initial' if side==0 else 'middle';after='middle' if side==0 else 'value';s+='open JGs_Libra JGs_LibraEnd\n'
 s+=f'''theorem step{side} : FIo_Native.weights.factored_s2_libra_weights_loop.body JGq_Powers0.a4 JGq_Powers1.a4
    (FIo_Install.toWeights JGo_TX2_WeightData.value).extra {{start:={side}#usize,«end»:=2#usize}} {before}=
    ok (.cont ({{start:={side+1}#usize,«end»:=2#usize}},{after})) := by
  unfold FIo_Native.weights.factored_s2_libra_weights_loop.body
  rw [JGo_TX2_Range.next {side}#usize 2#usize {side+1}#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [extra{side},bind_tc_ok,power{side}_0,bind_tc_ok,power{side}_1,bind_tc_ok,power{side}_2,bind_tc_ok,power{side}_3,bind_tc_ok]
  have read2 : Array.index_usize (Array.make 4#usize [FIo_Native.aspis_core.field.QM31.ONE,q{side}_1,q{side}_2,q{side}_3]) 2#usize=ok q{side}_2 := by rfl
  rw [read2,bind_tc_ok,power{side}_4,bind_tc_ok,power{side}_5,bind_tc_ok,power{side}_6,bind_tc_ok,power{side}_7,bind_tc_ok]
  have low : FIo_Native.weights.Weights.scalar_factor (Array.make 4#usize [FIo_Native.aspis_core.field.QM31.ONE,q{side}_1,q{side}_2,q{side}_3]) JGq_Powers0.a4=ok JGs_LibraScale{side}.value := by
    with_unfolding_all exact JGs_LibraScale{side}.source
  rw [low,bind_tc_ok]
'''
 for t in range(4):
  s+=f'''  have perm{t} : Array.index_usize FIo_Native.weights.PERM {t}#usize=ok {perm[t]}#usize := by with_unfolding_all rfl
  have ap{t} : Array.index_usize JGq_Powers1.a4 {perm[t]}#usize=ok JGq_Powers1.p{perm[t]} := by rfl
  have qp{t} : Array.index_usize (Array.make 4#usize [FIo_Native.aspis_core.field.QM31.ONE,q{side}_4,q{side}_8,q{side}_12]) {t}#usize=ok q{side}_{4*t} := by with_unfolding_all rfl
  rw [perm{t},bind_tc_ok,ap{t},bind_tc_ok,qp{t},bind_tc_ok,mixed{side}_{t},bind_tc_ok,quarter{side}_{t},bind_tc_ok]
'''
 # array reads across term arrays must be reduced before sum theorems
 for t in range(4):
  s+=f'  have tr{t} : Array.index_usize (Array.make 4#usize [term{side}_0,term{side}_1,term{side}_2,term{side}_3]) {t}#usize=ok term{side}_{t} := by rfl\n'
 s+=f'  rw [tr0,bind_tc_ok,tr1,bind_tc_ok,sum{side}call2,bind_tc_ok,tr2,bind_tc_ok,sum{side}call3,bind_tc_ok,tr3,bind_tc_ok,sum{side}call4,bind_tc_ok]\n'
 if side==0:s+='  simp only [ite_true]\n  rw [call_a,bind_tc_ok,JGs_LibraWrites.up0,bind_tc_ok,call_b,bind_tc_ok,call_c,bind_tc_ok,JGs_LibraWrites.up1,bind_tc_ok]\n'
 else:
  s+='''  simp only [show ¬(1#usize=0#usize) from by decide,ite_false]
  rw [JGs_LibraWrites.read,bind_tc_ok,ap3,bind_tc_ok,call_d,bind_tc_ok,call_e,bind_tc_ok,call_f,bind_tc_ok,
    JGs_LibraWrites.up2,bind_tc_ok,call_g,bind_tc_ok,call_h,bind_tc_ok,JGs_LibraWrites.up3,bind_tc_ok,
    call_i,bind_tc_ok,power1_8,bind_tc_ok,call_j,bind_tc_ok,JGs_LibraWrites.up4,bind_tc_ok]
'''
 s+=f'#print axioms step{side}\n'+end(ns);out[f'JGs_LibraNative{side}']=s
ns='JGs_LibraSource';s=head(['JGs_LibraNative0','JGs_LibraNative1'],ns)
s+='''abbrev S := core.ops.range.Range Usize × Array FIo_Install.NE 4#usize
def states : Nat → S
  | 0 => ({start:=0#usize,«end»:=2#usize},JGs_LibraEnd.initial)
  | 1 => ({start:=1#usize,«end»:=2#usize},JGs_LibraEnd.middle)
  | _ => ({start:=2#usize,«end»:=2#usize},JGs_LibraEnd.value)
theorem source : FIo_Native.weights.factored_s2_libra_weights JGq_Powers0.a4 JGq_Powers1.a4
    (FIo_Install.toWeights JGo_TX2_WeightData.value).extra=ok JGs_LibraEnd.value := by
  unfold FIo_Native.weights.factored_s2_libra_weights FIo_Native.weights.factored_s2_libra_weights_loop
  apply JGo_TX2_LoopChain.source
    (fun t : S=>FIo_Native.weights.factored_s2_libra_weights_loop.body JGq_Powers0.a4 JGq_Powers1.a4
      (FIo_Install.toWeights JGo_TX2_WeightData.value).extra t.1 t.2) states 2 JGs_LibraEnd.value
  · intro i hi
    interval_cases i
    · exact JGs_LibraNative.step0
    · exact JGs_LibraNative.step1
  · unfold FIo_Native.weights.factored_s2_libra_weights_loop.body
    with_unfolding_all rfl
#print axioms source
''';out[ns]=s+end(ns)
# Retire the memory-rejected concrete-parent emitters permanently.
# JGs_libra_stages.py emits the active generic-forward parent path.
out.pop('JGs_LibraNative0',None)
out.pop('JGs_LibraNative1',None)
out.pop('JGs_LibraSource',None)
for mod,s in out.items():
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert (p if p.exists() else R/'evidence/fixture-tx2p-20261027/JGs_UNCHECKED'/(p.name+'.txt')).read_text()==s,mod
 else:p.write_text(s)
print(len(out),'bounded Libra modules; archived candidates require fresh Lean checks under own prefix')
