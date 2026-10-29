"""Keep projected output stores explicit and bind each of its four source cells."""
exec(open('tools/pv-b3p6-20261028/projected_stages227_resume13.py').read().split('records=[]')[0])
chunk='\n'.join(lines[starts[0]:starts[1]])
chunk=chunk.replace('Std.Usize.wrapping_mul 4#usize 0#usize','Std.Usize.wrapping_mul 4#usize group')
chunk=chunk.replace('Array.index_usize leading 0#usize','Array.index_usize leading group').replace('Array.index_usize full 0#usize','Array.index_usize full group')
s='import PV_B3P_ProjectedBridge13227\nimport PV_B3P_FourStores13227\n'+header+'def projected_compute13 '+shared+' (group : Usize) : Result aspis_core.field.QM31 := do\n'+chunk+'\n  .ok q32\nend PV_B3P_Binding13227\n';(L/'PV_B3P_ProjectedCompute13227.lean').write_text(s)
outputs=['q32','q47','q62','q77']
for k in range(4):
 prev=' '.join(outputs[:k]);pars=shared+(f' ({prev} : aspis_core.field.QM31)'if prev else '')
 result='projected_stage13_'+str(k+1)+' '+args+' '+(prev+' 'if prev else '')+'value' if k<3 else '.ok (Array.make 4#usize ['+','.join(outputs[:k]+['value'])+'])'
 s='import PV_B3P_ProjectedCompute13227\n'+header
 s+='theorem projected_cell_binding13_'+str(k)+' '+pars+' :\n    projected_stage13_'+str(k)+' '+args+' '+prev+' = (do\n      let value ← projected_compute13 '+args+' '+str(k)+'#usize\n      '+result+') := by\n'
 s+='  unfold projected_stage13_'+str(k)+' projected_compute13\n  simp only [PV_B3P_Ordered227.bind_assoc,PV_B3P_Binding12227.bind_return12]\n'
 s+='#print axioms projected_cell_binding13_'+str(k)+'\nend PV_B3P_Binding13227\n'
 (L/('PV_B3P_ProjectedCell13'+str(k)+'227.lean')).write_text(s)
