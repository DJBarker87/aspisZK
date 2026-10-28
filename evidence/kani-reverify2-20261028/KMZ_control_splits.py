from KMZ_driver import *
for number,stage,part in [(30,4,'prefix'),(31,4,'appended')]:
 a=f'KMZ_K{number:03}'
 if (E/a/'receipt.json').exists():continue
 parent=f'KMY_K{40+stage:03}';cfg=json.loads((OLD/(parent+'.json')).read_text());src=(OLD/'sources'/(archive[parent]['KMY_windows.rs']+'.txt')).read_text()
 start=src.index('fn wide_append_stage');at=src.index('assert_eq!(out[j],',start)
 src=src[:at]+f'kani::assume(j{ "<" if part=="prefix" else ">="}LEN);\n '+src[at:]
 at=src.index('assert_eq!(out[j],',start);src=src[:at]+src[at:].replace('assert_eq!(out[j],','assert_eq!(out[j] ^ 1u8,',1)
 h=f'KMY_wide_stage{stage}';src=src.replace('fn '+h+'(', 'fn '+h+'_selected(').replace('KMY_','KMZ_').replace('KMZ_field.rs','KMY_field.rs')
 cfg.update(sources=[x.replace('KMY_windows.rs','KMZ_windows.rs').replace('KMY_gate.py','KMZ_gate.py') for x in cfg['sources']],command=['python3','KMZ_gate.py',a,h.replace('KMY_','KMZ_')+'_selected'],negative_control=True,parent_gate=parent,parent_harness=h,split=part,replaces_timeout=f'KMZ_K{11 if stage==4 else 12:03}',note='Changed the selected-byte domain to the prefix/appended window; the two windows partition the original assertion. Reporting flags do not change proof semantics.')
 result=run(a,cfg,src)
 if result!='COUNTEREXAMPLE':print('UNRESOLVED control',a,result,flush=True)
