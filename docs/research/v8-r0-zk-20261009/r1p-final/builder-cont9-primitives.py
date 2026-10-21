#!/usr/bin/env python3
"""Generate symbolic function identities, never concrete recurrence cells."""
import pathlib,re,sys
H=pathlib.Path(__file__).resolve().parent;L=H.parent/'lean'
s=(L/'R1Z/BuilderBankExtracted.lean').read_text()
out=['import R1Z.BuilderInverseResult','', '/-! Symbolic identities for duplicate primitive extractions. Every recursive', 'identity uses a decreasing suffix bound; no concrete cell is evaluated. -/', 'set_option autoImplicit false','namespace R1Z.BuilderPrimitiveDigests','open Aeneas Aeneas.Std Result R0Z.WriterRefine','open AspisBuilderGlueSource','']
prev=[]; audits=[]
for prefix,target,tag in [('aspis_r0_block_writer_copies','R0BlockCopies','block'),('aspis_r0_poseidon_copy','R0PoseidonCopy','poseidon')]:
 matches=list(re.finditer(r'^def '+prefix+r'\.(\w+)\b',s,re.M))
 for m in matches:
  name=m[1]; start=m.end(); end=s.index(':=',start);hdr=s[start:end].strip()
  body=s[end:s.index('\n/--',end)]
  # Constants have no binders; direct unrolling of their array definitions is small.
  j=0;params=[]
  while j<len(hdr) and hdr[j]=='(':
   k=j+1;depth=1
   while depth:
    if hdr[k]=='(':depth+=1
    if hdr[k]==')':depth-=1
    k+=1
   names,ty=hdr[j+1:k-1].split(':',1)
   params.append((names.strip().split(),ty.strip()))
   j=k
   while j<len(hdr) and hdr[j].isspace():j+=1
  vars=[x for ns,ty in params for x in ns]
  binders=' '.join('('+' '.join(ns)+' : '+ty+')' for ns,ty in params)
  args=' '.join(vars);tn=tag+'_'+name
  lhs=prefix+'.'+name;rhs=target+'.'+name
  out+=['theorem '+tn+' '+binders+' :',f'    {lhs} {args} = {rhs} {args} := by']
  guard=re.search(r'if (\w+) < (\d+)#usize',body)
  if 'partial_fixpoint' in body:
   assert guard,(name,'unknown recurrence shape')
   idx,bound=guard.groups();assert vars[-1]==idx
   other=vars[:-1]
   out += [f'  generalize he : {bound}-{idx}.val = remaining',f'  induction remaining using Nat.strong_induction_on generalizing '+args+' with','  | h remaining ih =>',f'    rw [{lhs},{rhs}]',f'    by_cases hit : {idx}.val < {bound}',f'    · have ht : {idx} < {bound}#usize := by simpa [UScalar.lt_equiv] using hit',f'      have hn : (Usize.wrapping_add {idx} 1#usize).val = {idx}.val+1 := by',f'        rw [uadd _ _ (by simp; omega)]; rfl']
   obinders=' '.join('('+' '.join(ns)+' : '+ty+')' for ns,ty in params[:-1])
   nidx=f'(Usize.wrapping_add {idx} 1#usize)'
   oargs=' '.join(other)
   out += [f'      have hnext : ∀ {obinders},',f'          {lhs} {oargs} {nidx} = {rhs} {oargs} {nidx} := by',f'        intros '+oargs,f'        exact ih ({bound}-{nidx}.val) (by omega) {oargs} {nidx} rfl',f'      simp only [if_pos ht,lift,bind_tc_ok,hnext'+(','+','.join(prev) if prev else '')+']',f'    · have ht : ¬{idx} < {bound}#usize := by simpa [UScalar.lt_equiv] using hit',f'      simp only [if_neg ht]']
  else:
   out+=['  simp only ['+','.join([lhs,rhs,*prev])+']']
  out+=[''];prev.append(tn);audits.append(tn)
out += ['#print axioms '+n for n in audits]+['end R1Z.BuilderPrimitiveDigests','']
p=L/'R1Z/BuilderPrimitiveDigests.lean';content='\n'.join(out)
if '--check' in sys.argv:assert p.read_text()==content
else:p.write_text(content)
print(len(audits),'symbolic identities; exceptional concrete cells: none')
