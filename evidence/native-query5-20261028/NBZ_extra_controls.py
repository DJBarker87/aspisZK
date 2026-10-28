from pathlib import Path
import json,difflib
E=Path(__file__).resolve().parent
s=Path('/tmp/NBZ_inherited_native.rs').read_text().replace('NBW_','NBZ_EX_')
rows=[];extra=[]
for old,expected,wrong,positive in [
 ('NBZ_EX_NBB_add_frame','assert_eq!(row[k],if k==j {NBZ_EX_NBB_REPLY} else {before})','assert_ne!(row[k],if k==j {NBZ_EX_NBB_REPLY} else {before})','NBW_K046'),
 ('NBZ_EX_NBB_fold_frame','assert_eq!(row[k],if j==k {NBZ_EX_NBB_REPLY} else {before[k]})','assert_ne!(row[k],if j==k {NBZ_EX_NBB_REPLY} else {before[k]})','NBW_K047'),
 ('NBZ_EX_NBB_push_selected_frame','assert_eq!(row[limb],NBZ_EX_NBB_OUT[limb])','assert_ne!(row[limb],NBZ_EX_NBB_OUT[limb])','NBW_K048'),
 ('NBZ_EX_initializer_window','assert_eq!(raw[k],NBZ_EX_qwords(q)[k]as u64)','assert_ne!(raw[k],NBZ_EX_qwords(q)[k]as u64)','NBW_K050')]:
 p=s.index('fn '+old+'(');a=s.rfind('#[kani::proof]',0,p);b=s.index('{',p)+1;d=1
 while d:d+=(s[b]=='{')-(s[b]=='}');b+=1
 body=s[p:b];assert expected in body
 body=body.replace(expected,wrong,1).replace('fn '+old+'(','fn '+old+'_negative(',1)
 extra.append(s[a:p]+body);rows.append(dict(harness='verifier::candidate::NBZ_extra_controls::'+old+'_negative',inherited_positive=positive,negative=True,scope='matched false-value control to an inherited additional NBW local pass'))
s+='\n'+'\n'.join(extra)+'\n'
Path('/tmp/NBZ_extra_controls_generated.rs').write_text(s)
(E/'NBZ_extra_controls.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBZ_extra_controls.rs')))
(E/'NBZ_EXTRA_PLAN.json').write_text(json.dumps(rows,indent=2)+'\n')
