from pathlib import Path
import re
root=Path(__file__).resolve().parents[2]
p=root/'lean/R22Stage2LeafTotal.lean'; s=p.read_text(); a=s.index('theorem r22_checked_add_eq') if 'theorem r22_checked_add_eq' in s else s.index('/-- Exact evaluation'); b=s.index('theorem r22_index_at_total')
header='''theorem r22_checked_add_eq (a b c : Usize) (h : a.val+b.val=c.val) :
    (a+b : Result Usize) = ok c := by
  obtain ⟨z,hz,hv⟩ := AspisR1.R22Stage2ControlBounds.add_total a b (by rw [h]; scalar_tac)
  have he : z=c := UScalar.eq_of_val_eq (by omega)
  simpa only [he] using hz

theorem r22_checked_mul_eq (a b c : Usize) (h : a.val*b.val=c.val) :
    (a*b : Result Usize) = ok c := by
  obtain ⟨z,hz,hv⟩ := AspisR1.R22Stage2ControlBounds.mul_total a b (by rw [h]; scalar_tac)
  have he : z=c := UScalar.eq_of_val_eq (by omega)
  simpa only [he] using hz

theorem r22_checked_sub_eq (a b c : Usize) (hle : b.val ≤ a.val)
    (h : a.val-b.val=c.val) : (a-b : Result Usize) = ok c := by
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (UScalar.sub_spec (x := a) (y := b) hle)
  have he : z=c := UScalar.eq_of_val_eq (by omega)
  simpa only [he] using hz

'''
body=(root/'lean/R22Stage2LocalBodies.lean').read_text()
base={'compact.FINAL_LEN':64,'compact.HEADER':16,'compact.QUERIES':22,'compact.OFF_SEMANTIC':16}
constants=dict(base); values={}; proofs=[]
for m in re.finditer(r'^def ([\w.]+) : Result Std.Usize := (.*?)(?=\n\ndef|\n\nend)',body,re.S|re.M):
 name=m[1]; text=m[2]
 if name.startswith('multiproof.'): continue
 text=text.replace('do\n','').strip(); env={}; hs=[]
 def val(x):
  x=x.strip()
  if '#usize' in x:return int(x.split('#')[0])
  if x in env:return env[x]
  return constants[x]
 try:
  for line in text.splitlines():
   line=line.strip(); mm=re.match(r'let (\w+) ← (.*)',line); expr=mm[2] if mm else line
   op=re.match(r'(.*?) ([+*\-]) (.*)',expr)
   if op:
    aa,bb=val(op[1]),val(op[3]); cc={'+':lambda:aa+bb,'*':lambda:aa*bb,'-':lambda:aa-bb}[op[2]](); idx=len(hs); tag={'+':'add','*':'mul','-':'sub'}[op[2]]
    hs.append(f'  have h{idx} : ({aa}#usize {op[2]} {bb}#usize : Result Usize) = ok {cc}#usize := by\n    apply r22_checked_{tag}_eq <;> decide')
   else: cc=val(expr)
   if mm:env[mm[1]]=cc
  short='r22_'+name.replace('.','_')+'_total'
  proofs.append(f'theorem {short} : {name} = ok {cc}#usize := by\n'+'\n'.join(hs)+'\n  simp only ['+', '.join([name]+[v for k,v in values.items() if k in text]+[k for k in base if k in text or (k=='compact.HEADER' and 'compact.OFF_SEMANTIC' in text)]+[f'h{i}' for i in range(len(hs))]+['bind_tc_ok'])+']\n')
  constants[name]=cc; values[name]=short
 except (KeyError,ValueError):pass
s=s[:a]+header+'\n'.join(proofs)+'\n'+s[b:]; s=s[:s.index('#print axioms')]+''.join('#print axioms '+n+'\n' for n in ['r22_checked_add_eq','r22_checked_mul_eq','r22_checked_sub_eq']+list(values.values())+['r22_index_at_total','r22_value_at_total'])+'end AspisR1Stage2\n'; p.write_text(s)
print(len(proofs),constants)
