from pathlib import Path
E=Path(__file__).parent
s=(E/'NNH_HostClaims.lean').read_text()
pre,body=s.split('def conclusion',1)
header,expr=body.split('    MultiproofConeP6Frozen2Stage.P6Boundary',1)
expr='MultiproofConeP6Frozen2Stage.P6Boundary'+expr.split('\n#print axioms',1)[0]
parts=[];depth=0;start=0
for k,ch in enumerate(expr):
 if ch in '({[':depth+=1
 elif ch in ')}]':depth-=1
 elif ch=='∧' and depth==0:parts.append(expr[start:k].strip());start=k+1
parts.append(expr[start:].strip())
assert len(parts)==11,len(parts)
pre=pre.replace('namespace AspisR1.NNH_HostClaims','namespace AspisR1.NNH_HostSplit').replace('import NNH_HostCtx','import NNH_HostClaims')
out=pre+'def rest'+header+'    '+(' ∧\n    '.join(parts[:3]+parts[4:]))+'\n\ndef outcome'+header+'    '+parts[3]+'''

theorem conclusion_iff (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second) :
 NNH_HostClaims.conclusion L copy c n1 n2 ↔ rest L copy c n1 n2 ∧ outcome L copy c n1 n2 := by
 unfold NNH_HostClaims.conclusion rest outcome
 dsimp only
 constructor
 · rintro ⟨a,b,c,d,e,f,g,h,i,j,k⟩
   exact ⟨⟨a,b,c,e,f,g,h,i,j,k⟩,d⟩
 · rintro ⟨⟨a,b,c,e,f,g,h,i,j,k⟩,d⟩
   exact ⟨a,b,c,d,e,f,g,h,i,j,k⟩
#print axioms conclusion_iff
end AspisR1.NNH_HostSplit
end
'''
(E/'NNH_HostSplit.lean').write_text(out)
