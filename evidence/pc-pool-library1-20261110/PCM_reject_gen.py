"""Add child-domain-conditional rejection witnesses to wrapper draft modules."""
from pathlib import Path
E=Path(__file__).resolve().parent
rows=[
 (311,'(decoder : Decoder) (a : Args)','decoder','decoder.call a','.invalidAccountData',None),
 (312,'(decoder : Decoder) (a : Args)','decoder','decoder.call (a,true)','.invalidAccountData',None),
 (313,'(decoder : Decoder) (a : Args)','decoder','decoder.call (a,false)','.invalidAccountData',None),
 (304,'(decoder : Decoder) (a : Args)','decoder','decoder.call (a,true)','.invalidAccountData',None),
 (314,'(decoder : Decoder) (a : Args)','decoder','decoder.call a','.invalidInstructionData','.invalidInstructionData'),
 (319,'(C : Children) (a : Args)','C','C.nextLane.call a','.custom 0x41532003',None),
 (326,'(C : Children) (a : Args)','C','C.append.call (a.1.tree,a.2.2,EMPTY_ROOTS)','.custom 0x41532003','.custom 0x41532003'),
 (337,'(encoder : Encoder) (a : TerminalResult)','encoder','encoder.call a','.custom 0x4153202d','.custom 0x4153202d'),
 (347,'(C : Children) (a : Args)','C','C.plan.call a','.invalidInstructionData',None),
 (348,'(C : Children) (runtime : Runtime) (a : Args)','C runtime','C.requireProgram.call (a.verifier_program,a.plan.selected_verifier)','.custom 0x41532027',None),
 (358,'(C : Children) (a : Args)','C','C.rentGet.call ()','.unsupportedSysvar',None),
 (356,'(sdkInvoke : Child Args Unit) (a : Args)','sdkInvoke','sdkInvoke.call a','.accountBorrowFailed',None),
 (357,'(sdkInvokeSigned : Child Args Unit) (a : Args)','sdkInvokeSigned','sdkInvokeSigned.call a','.accountBorrowFailed',None),
 (294,'(C : Children) (a : Args)','C','C.encode.call a.2.2','.custom 0x41532025','.custom 0x41532025')]
for n,params,lib,first,err,mapped in rows:
 p=E/f'PCM_Spec_POOL_{n}.lean';s=p.read_text();s='import PCM_Rejection\nimport PCM_StepLaws\n'+s
 result= mapped or err
 tactic='rw [early,PCM.Computation.mapError_throw,PCM.Computation.bind_throw]' if mapped else 'rw [early,PCM.Computation.bind_throw]'
 if n in [356,357]:tactic='exact early'
 # Explicit actual own-input early rejection; no child success hypothesis.
 code=f'''
/-- At a real rejecting argument, dropping the exact child error is rejected.
`early` is supplied by the named child's canonical graph at these arguments;
this lemma is supporting work and never a parent row root. -/
theorem rejects_wrong_error {params}
    (early : {first} = PCM.Computation.throw ({err})) :
    ¬ RowSpec {lib} (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  apply PCM.rejects_error (fun _ => True) (Ref {lib}) a ({result}) .invalidArgument trivial
  · unfold Ref
    {tactic}
  · intro h; cases h
#print axioms rejects_wrong_error
'''
 p.write_text(s.replace(f'end PCM_POOL_{n}',code+f'end PCM_POOL_{n}'))
print('PCM wrapper rejection lemmas added with explicit child graph obligations')
