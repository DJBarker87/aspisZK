from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2]
x={'__file__':str(R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py')};exec((R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py').read_text().split('mods,results=generate()')[0],x)
def q(v):return '⟨⟨%s#u32,%s#u32⟩,⟨%s#u32,%s#u32⟩⟩'%tuple(v)
def header(imports,ns):return '\n'.join('import '+i for i in imports)+f'\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.{ns}\nopen Aeneas Aeneas.Std Result ControlFlow\n'
def end(ns):return f'end AspisR1.{ns}\nend\n'
out={}; prior=[[0]*4 for _ in range(64)]
for k in [1,3,4]:
 ns=f'JGs_T{k}';before=[a[:] for a in prior];current=[a[:] for a in prior];current[0]=[1,0,0,0]
 states=[current[:]];steps=[];bounds=[]
 for d,n in [(2,1),(3,4),(4,16)]:
  digits=x['nums']('JGo_TX2_WeightData',f'f{k}{d}');digits=[digits[a:a+4] for a in range(0,16,4)]
  start=len(steps)
  for j in reversed(range(n)):
   v=current[j]
   for s in range(4):current[j+s*n]=x['qmul'](v,digits[s])
   steps.append((d,n,j));states.append(current[:])
  bounds.append((d,n,start,len(steps)))
 s=header(['JGq_PairShape','FJa_ReverseStep','JGo_TX2_LoopChain'],ns)
 for i,v in enumerate([before]+states):
  tag='input' if i==0 else f's{i-1}'
  s+=f'def {tag} : Slice FIo_Install.NQ := ⟨['+','.join(q(z) for z in v)+'],by simp;scalar_tac⟩\n'
 s+=end(ns);out[ns+'Data']=s
 size=4 if k==1 else 8
 chunks=(21+size-1)//size
 for chunk in range(chunks):
  ids=range(chunk*size,min(chunk*size+size,21))
  if not ids:continue
  s=header([ns+'Data'],ns)
  for i in ids:
   d,n,j=steps[i]
   s+=f'''theorem step{i} : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w {k}#usize {n}#usize {d}#usize
    (FJa_ReverseStep.cursor {j+1}#usize) s{i}=ok (.cont (FJa_ReverseStep.cursor {j}#usize,s{i+1})) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step {j+1}#usize (by decide)
  have eq : idx={j}#usize := UScalar.eq_of_val_eq (by change idx.val={j};change idx.val+1={j+1} at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
{''.join(f'  have mul{t} : Usize.wrapping_mul {t}#usize {n}#usize={t*n}#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value {t}#usize {n}#usize (by decide))\n  have add{t} : Usize.wrapping_add {j}#usize {t*n}#usize={j+t*n}#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value {j}#usize {t*n}#usize (by decide))\n' for t in range(4))}  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step{i}
'''
  s+=end(ns);out[ns+f'Step{chunk}']=s
 s=header([ns+f'Step{i}' for i in range(chunks)],ns)
 for d,n,lo,hi in bounds:
  s+=f'def states{d} : Nat → FJa_ReverseStep.Rev × Slice FIo_Install.NQ\n'
  for i in range(n):s+=f'  | {i} => (FJa_ReverseStep.cursor {n-i}#usize,s{lo+i})\n'
  s+=f'  | _ => (FJa_ReverseStep.cursor 0#usize,s{hi})\n'
  s+=f'''theorem inner{d} : FIo_Native.weights.Weights.tensor_loop0_loop0 (FJa_ReverseStep.cursor {n}#usize)
    JGq_PairShape.w {k}#usize s{lo} {n}#usize {d}#usize=ok (JGq_PairShape.w,s{hi}) := by
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0
  apply JGo_TX2_LoopChain.source
    (fun t : FJa_ReverseStep.Rev × Slice FIo_Install.NQ=>FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w {k}#usize {n}#usize {d}#usize t.1 t.2)
    states{d} {n} (JGq_PairShape.w,s{hi})
  · intro i hi
    interval_cases i
'''
  for i in range(n):s+=f'    · exact step{lo+i}\n'
  s+=f'  · change FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w {k}#usize {n}#usize {d}#usize (FJa_ReverseStep.cursor 0#usize) s{hi}=ok (.done (JGq_PairShape.w,s{hi}))\n    unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body\n    have stop := FJa_ReverseStep.stop\n    unfold FJa_ReverseStep.next at stop\n    rw [stop,bind_tc_ok]\n    rfl\n#print axioms inner{d}\n'
  s+=f'''theorem outer{d} : FIo_Native.weights.Weights.tensor_loop0.body {k}#usize
    {{start:={d}#usize,«end»:=5#usize}} JGq_PairShape.w s{lo} {n}#usize=
    ok (.cont ({{start:={d+1}#usize,«end»:=5#usize}},JGq_PairShape.w,s{hi},{n*4}#usize)) := by
  unfold FIo_Native.weights.Weights.tensor_loop0.body
  rw [JGo_TX2_Range.next {d}#usize 5#usize {d+1}#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have rev : core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
      ({{start:=0#usize,«end»:={n}#usize}} : core.ops.range.Range Usize)=ok (FJa_ReverseStep.cursor {n}#usize) := by rfl
  rw [rev,bind_tc_ok,inner{d},bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok]
  have wrap : Usize.wrapping_mul {n}#usize 4#usize={n*4}#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value {n}#usize 4#usize (by decide))
  rw [wrap]
#print axioms outer{d}
'''
 s+='''abbrev S := core.ops.range.Range Usize × FIo_Native.weights.Weights × Slice FIo_Install.NQ × Usize
def outerStates : Nat → S
  | 0 => ({start:=2#usize,«end»:=5#usize},JGq_PairShape.w,s0,1#usize)
  | 1 => ({start:=3#usize,«end»:=5#usize},JGq_PairShape.w,s1,4#usize)
  | 2 => ({start:=4#usize,«end»:=5#usize},JGq_PairShape.w,s5,16#usize)
  | _ => ({start:=5#usize,«end»:=5#usize},JGq_PairShape.w,s21,64#usize)
'''
 s+=f'''theorem source : FIo_Native.weights.Weights.tensor JGq_PairShape.w {k}#usize 2#usize input=ok s21 := by
  have init : Slice.update input 0#usize FIo_Native.aspis_core.field.QM31.ONE=ok s0 := by with_unfolding_all rfl
  unfold FIo_Native.weights.Weights.tensor
  rw [init,bind_tc_ok]
  unfold FIo_Native.weights.Weights.tensor_loop0
  apply JGo_TX2_LoopChain.source
    (fun t : S=>FIo_Native.weights.Weights.tensor_loop0.body {k}#usize t.1 t.2.1 t.2.2.1 t.2.2.2)
    outerStates 3 s21
  · intro i hi
    interval_cases i
    · exact outer2
    · exact outer3
    · exact outer4
  · unfold FIo_Native.weights.Weights.tensor_loop0.body
    with_unfolding_all rfl
#print axioms source
'''
 s+=end(ns);out[ns]=s;prior=current
for mod,s in out.items():
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s,mod
 else:p.write_text(s)
print(len(out),'bounded tensor modules')
