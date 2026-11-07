from pathlib import Path
E=Path(__file__).resolve().parent
# Per-lexical-cut symbolic congruence. No raw reply is fixed to Ok.
rows={
'r9':('reply','r9, transcript3','val6','erase_mark5 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6'),
'r7':('r7',None,'vr2','erase_r8 c s alpha val1 val3 state_before_z0 transcript2 val4 vr2 r7'),
'r6':('reply','r6, transcript2','val4','erase_r7 c s alpha val1 val3 state_before_z0 transcript2 val4'),
'state_before_z0':('state_before_z0',None,'vr1','erase_r6 c s alpha transcript1 val1 val3 state_before_z0 vr1'),
'r5':('r5',None,'val3','erase_q1 c s running val2 mask alpha transcript1 val1 val3 r4'),
'r4':('r4',None,'vr','erase_r5 c s running val2 mask alpha transcript1 val1 vr r4'),
'r3':('r3',None,'val2','erase_mark3 c s running val2 alpha transcript1 val1'),
'r1':('r1',None,'val1','erase_r2 c s running alpha transcript1 val1'),
'r':('r',None,'val','erase_mark2 c s val.1 val.2.1 val.2.2'),
'r8':('r8',None,'val5',None),
}
for name,(reply,pair,value,tail) in rows.items():
 p=E/('NNG_Erase_'+name+'.lean');s=p.read_text();a=s.index('  simp only');b=s.index('#print',a)
 lift='erase_liftM' if name=='r3' else 'NMT_CallTree.erase_invoke'
 proof=f'''  unfold NNG_TreeSuffixes.f_{name} NNG_SourceSuffixes.f_{name}
  rw [erase_bindM, {lift}]
  apply result_congr
  intro {reply}
'''
 if pair:proof+=f'  rcases {reply} with ⟨{pair}⟩\n'
 proof+='''  rw [erase_bindM, erase_liftM]
  apply result_congr
  intro cf
  cases cf with
'''
 if name=='r8':
  proof+='''  | Continue val5 =>
    rw [erase_bindM, erase_liftM]
    apply result_congr
    intro cf9
    cases cf9 with
    | Continue vr3 => exact erase_r9 c s alpha val1 val3 state_before_z0 transcript2 val4 val5 vr3
    | Break residual => exact NNG_TraceAlgebra.erase_lift _
'''
 else:proof+=f'  | Continue {value} => exact {tail}\n'
 proof+='  | Break residual => exact NNG_TraceAlgebra.erase_lift _\n'
 p.write_text(s[:a]+proof+s[b:])
