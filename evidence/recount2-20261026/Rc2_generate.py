from pathlib import Path
p=Path('lean')
# Keep the complete original base statement and strengthen its last, selected
# Claims tuple. No independent f/s/semantic execution is introduced.
s=(p/'Cons_Base.lean').read_text().replace('namespace AspisR1.Cons_Base','namespace AspisR1.Rc2_Base').replace('end AspisR1.Cons_Base','end AspisR1.Rc2_Base')
s='import NP6_ParsedClaims\nimport NP6_Constructors\n'+s
s=s.replace('(claimsStd : ClaimsUnrolledFinish.StdCalls)','(reservation : NP6_StdModel.Reservation)').replace('claimsStd','(NP6_StdModel.calls reservation)')
s=s.replace('= ok (.Ok (retainedSem sem).claims))','= ok (.Ok (retainedSem sem).claims) ∧\n          NP6_ClaimsRun.Content reservation claimsPrefix (retainedSem sem).claims ∧\n          NP6_ParsedClaims.Content reservation v.semantic claimsPrefix (retainedSem sem).claims)')
# Strengthening proof with all same witnesses through the last claims field.
head=s[s.index('def Outcome'):s.index(' : Prop :=')]
head=head.replace('def Outcome','theorem strengthen',1)
head += '''
    (base : Cons_Base.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps
      stageBase finishOps B (NP6_StdModel.calls reservation) program data1 data2 slot
      saved post1 post2 H f s outer pre middle fs ss run) :
    Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B
      reservation program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run := by
  obtain ⟨cuts,writer,reader,multiproof,scanY,checkY,scan,tx1,batches,header2,header1,
    expanded,owned,projectedRun,heap2,obs1,obs2,claims⟩ := base
  refine ⟨cuts,writer,reader,multiproof,scanY,checkY,scan,tx1,batches,header2,header1,
    expanded,owned,projectedRun,heap2,obs1,obs2,?_⟩
  obtain ⟨selected,selectedCall,selectedCuts,semantic,y1,v,sem,prefix,
    wide,semanticCall,parsed,normalized⟩ := claims
  exact ⟨selected,selectedCall,selectedCuts,semantic,y1,v,sem,prefix,
    wide,semanticCall,parsed,normalized,
    NP6_ClaimsRun.on_success reservation prefix _ normalized,
    NP6_ParsedClaims.on_success reservation v.semantic prefix _ parsed normalized⟩

#print axioms strengthen
'''
s=s.replace('end AspisR1.Rc2_Base',head+'end AspisR1.Rc2_Base')
(p/'Rc2_Base.lean').write_text('import Cons_Base\n'+s)
# New result factors the same shared tuple with strengthened base and initial.
s=(p/'T2R_FullResult.lean').read_text().replace('namespace AspisR1.T2R_FullResult','namespace AspisR1.Rc2_Result').replace('end AspisR1.T2R_FullResult','end AspisR1.Rc2_Result')
s='import Rc2_Base\n'+s
s=s.replace('(claimsStd : ClaimsUnrolledFinish.StdCalls)','(reservation : NP6_StdModel.Reservation)').replace('claimsStd','(NP6_StdModel.calls reservation)')
s=s.replace('Cons_Base.Outcome','Rc2_Base.Outcome').replace('finishOps B (NP6_StdModel.calls reservation) program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run ∧','finishOps B reservation program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run ∧\n      NP6_Constructors.Contents run.initial run.pending ∧')
(p/'Rc2_Result.lean').write_text(s)
