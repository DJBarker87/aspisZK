from pathlib import Path
R=Path(__file__).resolve().parents[2]
s=(R/'lean/FIq_CopyPrefix.lean').read_text();s=s[s.index('  let q ← Array.index_usize row.producer_values'):s.index('\n\n\nend FIq_Native')]
s=s.replace('row.','r.')
lines=s.strip().splitlines();proof=[];calls=[]
for line in lines:
 line=line.strip()
 if line.startswith('let '):
  name,expr=line[4:].split(' ← ')
 else:
  name='out';expr=line
 call='call_'+name;can='canon_'+name;calls.append(call)
 if expr.startswith('Array.index_usize '):
  expr=expr[len('Array.index_usize '):];arr,idx=expr.rsplit(' ',1)
  if arr.startswith('(Array.make'):
   canon='(by intro x hx; simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl|rfl|rfl|rfl <;> assumption)'
  else:canon={'r.producer_values':'hpv','r.consumer_values':'hcv','r.producer_weights':'hpw','r.consumer_weights':'hcw'}[arr]
  proof.append(f'  obtain ⟨{name},{call},{can}⟩ := JFy_ArrayTotal.read {arr} {idx} (by decide) {canon}')
 else:
  fn,x,y=expr.split();op=fn.split('.')[-1];fn='FIv_PreparedTotal.add' if op=='add' else 'JFy_FieldTotal.'+op
  def c(x):return {'chi':'hc','helper':'hh'}.get(x,'canon_'+x)
  proof.append(f'  obtain ⟨{name},{call},{can},_⟩ := {fn} {x} {y} {c(x)} {c(y)}')
proof+=['  refine ⟨out,?_,canon_out⟩','  unfold copy_residual','  rw ['+',bind_tc_ok,'.join(calls)+']']
p=R/'lean/JFy_CopyResidual.lean';text=p.read_text();a=text.index('  have spec :');b=text.index('#print axioms source');text=text[:a]+'\n'.join(proof)+'\n'+text[b:];p.write_text(text)
