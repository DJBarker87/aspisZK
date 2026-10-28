from pathlib import Path
import difflib,json
E=Path(__file__).resolve().parent
s=Path('/tmp/NBZ_observer_generated.rs').read_text();attrs=s[s.index('#[kani::proof]'):s.index('fn NBZ_observer_direct')]
rows=[]
for name,call,stub,positive in [('direct','NBZ_wrong(None,Phase::Query(0));','', 'NBZ_K071'),('stub','mark(None,Phase::Query(0));','NBZ_wrong','NBZ_K072'),('empty','NBZ_empty_case();','NBZ_wrong','NBZ_K073'),('full','NBZ_full_case();','NBZ_wrong','NBZ_K074')]:
 h='NBZ_observer_'+name+'_negative'
 s+=attrs+('' if not stub else '#[kani::stub(crate::verifier::mark,'+stub+')]\n')+'fn '+h+'(){'+call+'}\n'
 rows.append(dict(harness='verifier::candidate::NBZ_observer_controls::'+h,negative=True,inherited_positive=positive,diagnostic_only=True))
Path('/tmp/NBZ_observer_controls.rs').write_text(s)
(E/'NBZ_observer_controls.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBZ_observer_controls.rs')))
(E/'NBZ_OBSERVER_CONTROLS.json').write_text(json.dumps(rows,indent=2)+'\n')
