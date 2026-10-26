from pathlib import Path
L=Path('lean');s=(L/'Rc5_Top.lean').read_text()
s='import Rc5_Top\nimport Rc6_Result\nimport Rc6_Install\n'+s
s=s.replace('namespace AspisR1.Rc5_Top','namespace AspisR1.Rc6_Top').replace('end AspisR1.Rc5_Top','end AspisR1.Rc6_Top')
s=s.replace('Rc5_Result.Outcome','Rc6_Result.Outcome').replace('(p.physicalEvents t)) ∧','(p.physicalEvents t) hashv) ∧',1)
# Preserve entire old conclusion, adding P6 global boundary as first conjunct.
marker='    DrvC_Implementation.driver (Rc5_Install.configuration indexError c reservation) ='
s=s.replace(marker,'''    MultiproofConeP6Frozen2Stage.P6Boundary (P6C_Extension.dictionary hashv H) () H
      Op5T_P6.parent Op5T_P6.parent Op5T_P6.parent MultiproofConeP6Batch.referenceLeaf ∧
'''+marker,1)
s=s.split(' := by\n')[0]+''' := by
  obtain ⟨driverEq,sdkEq,original,headline,bound,zero,copyFacts,events,protection,trace,recorder⟩ :=
    Rc5_Top.deployed L sdk copy std allocator e1 e2 w1 w2 admission1 admission2 c indexError reservation
      native1 native2 hashv extraction sha256 H p1 syscall data1 data2 slot state1 state2 final1 final2
      saved post1 post2 accepted1 accepted2 root length prior words p t u actions game RuntimePersistence
      D P Q0 Q1 queries runtime raw binding adversary chooseSecond prefixBound choiceBound project select
  refine ⟨P6C_Extension.boundary hashv sha256 H p1 syscall,driverEq,sdkEq,?_,headline,bound,zero,
    copyFacts,events,protection,trace,recorder⟩
  exact Rc6_Result.strengthen L e1 e2 w1 w2
    (Rc5_Install.configuration indexError c reservation).adapter
    (Rc5_Install.configuration indexError c reservation).currentBase
    (Rc5_Install.configuration indexError c reservation).reserved
    (Rc5_Install.configuration indexError c reservation).query
    (Rc5_Install.configuration indexError c reservation).geometry
    (Rc5_Install.configuration indexError c reservation).stageBase
    (Rc5_Install.configuration indexError c reservation).finish c.boundaries reservation
    CPH_Program.verifier data1 data2 slot saved post1 post2 H
    (DrvC_Implementation.driver (Rc5_Install.configuration indexError c reservation)) prior
    (p.physicalEvents t) hashv native1 native2 extraction sha256 p1 syscall original

#print axioms deployed
end AspisR1.Rc6_Top
end
'''
s='import P6C_Extension\n'+s
(L/'Rc6_Top.lean').write_text(s)
