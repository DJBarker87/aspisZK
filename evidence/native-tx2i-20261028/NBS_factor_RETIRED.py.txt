from pathlib import Path
E=Path(__file__).resolve().parent
mapping={'JFr_TX2_ScalarRead':'NBS_ScalarRead','JFr_TX2_DotStep':'NBS_DotStep','JFr_TX2_DotLanes':'NBS_DotLanes','JFr_TX2_DotLaneTotal':'NBS_DotLaneTotal','JFs_TX2_Eight':'NBS_Eight','JFs_TX2_ArrayEight':'NBS_ArrayEight','JFs_TX2_FoldLane':'NBS_FoldLane','JFs_TX2_FoldEight':'NBS_FoldEight','JFs_TX2_Iterator':'NBS_Iterator','JFs_TX2_BatchWindow':'NBS_BatchWindow','JFs_TX2_OuterStep':'NBS_OuterStep','JFs_TX2_FromLimbs':'NBS_FromLimbs','JFs_TX2_DotSuffix':'NBS_DotSuffix','JFs_TX2_Inner':'NBS_DotInner','JFs_TX2_Outer':'NBS_DotOuter'}
for old,new in mapping.items():
 if new in ['NBS_DotInner','NBS_DotOuter']:continue
 s=Path('lean/'+old+'.lean').read_text()
 if old=='JFr_TX2_ScalarRead':s=s.replace('import JFr_TX2_Windows','import NBQ_FieldTotal\nimport FIp_NativeDots')
 if old=='JFs_TX2_OuterStep':pass
 for a,b in mapping.items():s=s.replace(a,b)
 s='/- Generic source/proof factoring from '+old+'; fixture-only imports removed. -/\n'+s
 Path('lean/'+new+'.lean').write_text(s)
# Own failed module replaced imports: no fixture modules needed.
p=Path('lean/NBS_DotTerm.lean');s=p.read_text().replace('import JFs_TX2_ArrayRead','import NBS_ArrayEight')
for a,b in mapping.items():s=s.replace(a,b)
s=s.replace('JFs_TX2_ArrayRead.source g term (by change term.val<29;omega)', 'array_read g term (by change term.val<29;omega)')
pos=s.index('/-- Input decoding domain.')
s=s[:pos]+'''theorem array_read {α : Type} {N : Usize} (a : Array α N) (j : Usize)
    (bound : j.val<N.val) : ∃ x, Array.index_usize a j=ok x ∧ x∈a.val := by
  let x := a.val[j.val]'(by rw [a.property];exact bound)
  refine ⟨x,?_,List.getElem_mem _⟩
  unfold Array.index_usize
  change (match a.val[j.val]? with | none => _ | some y => ok y)=ok x
  rw [List.getElem?_eq_getElem (by rw [a.property];exact bound)]
#print axioms array_read

'''+s[pos:]
p.write_text(s)
