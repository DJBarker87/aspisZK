from pathlib import Path
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
s=(L/'PV_RunJoin_CircleNeutralR24Tail53.lean').read_text();body=s.split('  let a1 :=')[1].split('  let c2 ←')[0];prefix='  let a1 :='+body.split('  let i8 ←')[0]
parts=[('i8','i18','out0'),('i18','i24','out1'),('i24','i33','out2'),('i33',None,'out3')]
for j,(start,end,out) in enumerate(parts):
 block='  let '+start+' ←'+body.split('  let '+start+' ←')[1]
 if end:block=block.split('  let '+end+' ←')[0]
 name=f'PV_RunJoin_R24Cell{j}_54'
 text='import R1Z.PV_RunJoin_CircleNeutralR24Tail53\nset_option autoImplicit false\nopen Aeneas Aeneas.Std Result ControlFlow\nnamespace R1Z.'+name+'\nabbrev Q := (U32 × U32) × (U32 × U32)\ndef cell (left right : Q) (u v : U64) : Result U32 := do\n'+prefix+block+'  ok '+out+'\n#print axioms cell\nend R1Z.'+name+'\n'
 (L/(name+'.lean')).write_text(text)
name='PV_RunJoin_R24Decompose54'
text='\n'.join('import R1Z.PV_RunJoin_R24Cell'+str(j)+'_54' for j in range(4))+'\nset_option autoImplicit false\nopen Aeneas Aeneas.Std Result ControlFlow\nnamespace R1Z.'+name+'\nabbrev Q := (U32 × U32) × (U32 × U32)\ntheorem complete (left right : Q) (u v : U64) :\n  PV_RunJoin_CircleNeutralR24Tail53.tail left right u v = (do\n'
for j in range(4):text+=f'    let x{j} ← PV_RunJoin_R24Cell{j}_54.cell left right u v\n'
text+='    let c0 ← PV_RunJoin_CircleR72Raw52.field.CM31.new x0 x1\n    let c1 ← PV_RunJoin_CircleR72Raw52.field.CM31.new x2 x3\n    ok (some (c0,c1))) := by\n  simp only [PV_RunJoin_CircleNeutralR24Tail53.tail,'+','.join('PV_RunJoin_R24Cell'+str(j)+'_54.cell' for j in range(4))+',bind_assoc_eq,bind_tc_ok]\n#print axioms complete\nend R1Z.'+name+'\n'
(L/(name+'.lean')).write_text(text)
