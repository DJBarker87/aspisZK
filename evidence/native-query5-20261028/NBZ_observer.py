from pathlib import Path
import json,difflib
E=Path(__file__).resolve().parent
s=Path('/tmp/NBZ_observer.rs').read_text()
attrs='''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::unwind(4096)]
'''
rows=[]
for name,call,stub in [('direct','NBZ_check(None,Phase::Query(0));',''),('stub','mark(None,Phase::Query(0));','NBZ_check'),('empty','NBZ_empty_case();','NBZ_check'),('full','NBZ_full_case();','NBZ_check')]:
 h='NBZ_observer_'+name
 s+=attrs+('' if not stub else '#[kani::stub(crate::verifier::mark,'+stub+')]\n')+'fn '+h+'(){'+call+'}\n'
 rows.append(dict(harness='verifier::candidate::NBZ_observer::'+h,case=name,diagnostic_only=True))
Path('/tmp/NBZ_observer_generated.rs').write_text(s)
(E/'NBZ_observer.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBZ_observer.rs')))
(E/'NBZ_OBSERVER_PLAN.json').write_text(json.dumps(rows,indent=2)+'\n')
