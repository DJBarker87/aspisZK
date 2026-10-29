"""Bind each raw suffix with one named theorem; peel binds instead of whole-body
normalization. This replaces rejected 66637, never raises recursion limits."""
exec(open('tools/pv-b3p6-20261028/projected_stages227_resume13.py').read().split('records=[]')[0])
# Variables from the exact segmented declaration, not new mathematical formulas.
outputs=['q32','q47','q62','q77'];prefix='\n'.join(lines[:starts[0]])
for k in range(3,-1,-1):
 prev=' '.join(outputs[:k]);pars=shared+(f' ({prev} : aspis_core.field.QM31)'if prev else '')
 tail='\n'.join(lines[starts[k]:]);chunk='\n'.join(lines[starts[k]:starts[k+1]if k<3 else len(lines)])
 binders=re.findall(r'^  let (\w+) ←',chunk,re.M)
 s='import PV_B3P_ProjectedStage13'+str(k)+'227\n'+('import PV_B3P_ProjectedRaw13'+str(k+1)+'227\n'if k<3 else '')+header
 s+='def projected_raw13_'+str(k)+' '+pars+' : Result (Array aspis_core.field.QM31 4#usize) := do\n'+tail+'\n'
 s+='theorem projected_raw_binding13_'+str(k)+' '+pars+' : projected_raw13_'+str(k)+' '+args+' '+prev+' = projected_stage13_'+str(k)+' '+args+' '+prev+' := by\n  unfold projected_raw13_'+str(k)+' projected_stage13_'+str(k)+'\n'
 for var in binders:s+='  apply congrArg (Aeneas.Std.bind _)\n  funext '+var+'\n'
 s+='  '+('exact projected_raw_binding13_'+str(k+1)+' '+args+' '+' '.join(outputs[:k+1])if k<3 else 'rfl')+'\n#print axioms projected_raw_binding13_'+str(k)+'\nend PV_B3P_Binding13227\n'
 (L/('PV_B3P_ProjectedRaw13'+str(k)+'227.lean')).write_text(s)
s='import PV_B3P_ProjectedPrefix13227\nimport PV_B3P_ProjectedRaw130227\n'+header+'''theorem projected_staging13
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors) :
    reference_poseidon.evaluate_state_only_poseidon_oracle_projected openings selectors =
      projected_prefix13 reference_poseidon.leading_pair_packed openings selectors := by
  unfold reference_poseidon.evaluate_state_only_poseidon_oracle_projected projected_prefix13
'''
for var in re.findall(r'^  let (\w+) ←',prefix,re.M):s+='  apply congrArg (Aeneas.Std.bind _)\n  funext '+var+'\n'
s+='  exact projected_raw_binding13_0 '+args+'\n'
s+='''theorem projected_actual_leading13
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors) :
    reference_poseidon.evaluate_state_only_poseidon_oracle_projected openings selectors =
      projected_prefix13 source_leading12 openings selectors :=
  Eq.trans (projected_staging13 openings selectors) (projected_prefix_leading13 openings selectors)
#print axioms projected_staging13
#print axioms projected_actual_leading13
end PV_B3P_Binding13227
''';(L/'PV_B3P_ProjectedBridge13227.lean').write_text(s)
