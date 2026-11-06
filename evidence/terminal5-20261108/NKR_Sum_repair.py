from pathlib import Path
import re
E=Path('/Users/dominic/ZK/.worktrees/cx-terminal5/evidence/terminal5-20261108')
p=E/'NKR_SumLookupCertificate.lean';s=p.read_text().replace('xs[i.val]=key','xs[i.val]?=some key').replace('    · exact same.symm','    · exact congrArg some same.symm').replace('    · simpa only [List.getElem_cons_succ] using read','    · simpa only [List.getElem?_cons_succ] using read')
s=s.replace('   rw [eq,group_key] at v\n   exact v','''   rw [eq] at v
   simpa only [List.getElem?_eq_getElem (by rw [group_length];exact (NJL_EndpointLookup.groupIndex index consumer bounds).isLt),group_key,Option.some.injEq] using v''')
s=s.replace('   rw [eq,pattern_key] at v\n   exact v','''   rw [eq] at v
   simpa only [List.getElem?_eq_getElem (by rw [pattern_length];exact (NJL_EndpointLookup.patternIndex index consumer bounds).isLt),pattern_key,Option.some.injEq] using v''')
p.write_text(s)
p=E/'NKR_SumRegroup.lean';s=p.read_text().replace(' fin_cases g <;> fin_cases h <;> norm_num [NJB_PatternReference.offset] at bg bh ⊢ <;> omega',' fin_cases g <;> fin_cases h <;> dsimp [NJB_PatternReference.offset] at bg bh ⊢ <;> first | rfl | omega');p.write_text(s)
p=E/'NKR_SumIntervals.lean';s=p.read_text();a=s.index('  have second :');b=s.index('\ndef off ',a);s=s[:a]+'''  have app:=@List.range'_append (off 0) (off n-off 0) (off (n+1)-off n) 1
  simpa only [Nat.one_mul,start,length] using app
''' +s[b:]
s=s.replace(' · have h := (NJL_TagData.interval ⟨n,small⟩).1.le\n   simpa only [off,Nat.min_eq_left (Nat.le_of_lt small),Nat.min_eq_left (by omega),',' · have h := (NJL_TagData.interval ⟨n,small⟩).1.le\n   have nextSmall : n+1≤30 := by omega\n   simpa only [off,Nat.min_eq_left (Nat.le_of_lt small),Nat.min_eq_left nextSmall,')
s=s.replace("   simp only [off,Nat.min_eq_right hn,Nat.min_eq_right hn']", "   simpa only [off,Nat.min_eq_right hn,Nat.min_eq_right hn'] using (Nat.le_refl (NJL_TagData.offsets ⟨30,by decide⟩))")
s=s.replace('theorem thirty : intervals off 30=List.range 272 := by\n rw [partition off monotone]\n rfl', '''theorem range_zero (n : Nat) : List.range' 0 n=List.range n := by
 apply List.ext_getElem
 · simp
 · intro i hi hj
   simp

theorem thirty : intervals off 30=List.range 272 := by
 have first : off 0=0 := rfl
 have last : off 30=272 := rfl
 rw [partition off monotone,first,last,Nat.sub_zero,range_zero]''').replace('#print axioms thirty','#print axioms range_zero\n#print axioms thirty');p.write_text(s)
p=E/'NKR_SumTagPermutation.lean';s=p.read_text().replace(',Bool.true_eq_true','').replace('Finite.surjective_of_injective (encoded domain) (injective domain cut)','Finite.surjective_of_injective (injective domain cut)');p.write_text(s)
p=E/'NKR_SumCopyTail.lean';s=p.read_text();s=re.sub(r'(NJB_ArrayCarrier.cell (?:values|weights)) ([0123])',r'\1 ⟨\2,by decide⟩',s);p.write_text(s)
p=E/'NKR_SumCopyInvocation.lean';s=p.read_text().replace(' simp only [reference,patternCall,scratchCall,finishCall,tailCall,bind_tc_ok]',''' simp only [reference,patternCall,scratchCall,finishCall,bind_tc_ok]
 change NKR_SumCopyTail.reference s values weights helper chi=ok {residual:=scaled,active:=active}
 exact tailCall''');p.write_text(s)
# A big-operator binder needs a parenthesized additive body; otherwise the
# second summand falls outside the binder and resolves a global name.
def wrap_pairs(s):
 pos=0
 while True:
  m=re.search(r'∑[^,\n]*,\s*\(',s[pos:])
  if not m:break
  start=pos+m.end()-1;d=1;k=start+1
  while d:d+=(s[k]=='(')-(s[k]==')');k+=1
  q=k
  while q<len(s) and s[q].isspace():q+=1
  if q<len(s) and s[q]=='+':
   q+=1
   while s[q].isspace():q+=1
   if s[q]=='(':
    d=1;end=q+1
    while d:d+=(s[end]=='(')-(s[end]==')');end+=1
    s=s[:start]+'('+s[start:end]+')'+s[end:];pos=end+2;continue
  pos=k
 return s
for name in ['NKR_SumTensorAlgebra.lean','NKR_SumCopyAssociation.lean']:
 p=E/name;p.write_text(wrap_pairs(p.read_text()))
p=E/'NKR_SumCopyAssociation.lean';s=p.read_text().replace(',Bool.true_eq_true','')
s=s.replace('∑ i : Fin 136,f i false+f i true','∑ i : Fin 136,(f i false+f i true)')
s=s.replace('∑ i : Fin 136,tagTerm lookup s g i false+tagTerm lookup s g i true','∑ i : Fin 136,(tagTerm lookup s g i false+tagTerm lookup s g i true)')
p.write_text(s)
p=E/'NKR_SumCopyRoot.lean';s=p.read_text();s=re.sub(r'using (hv|hw) ([0123])',r'using \1 ⟨\2,by decide⟩',s)
s=s.replace('  simp only [NKR_SumCopyInvocation.reference,patternCall,collectCall,finishCall,tailCall,bind_tc_ok]','''  simp only [NKR_SumCopyInvocation.reference,patternCall,collectCall,finishCall,bind_tc_ok]
  change NKR_SumCopyTail.reference s values weights helper chi=ok {residual:=scaled,active:=active}
  exact tailCall''');p.write_text(s)
print('Combined/Association/Root diagnostics batch repaired without limits changes')
