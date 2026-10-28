from pathlib import Path
import difflib,json
E=Path(__file__).resolve().parent
s=Path('/tmp/NBZ_windows.rs').read_text()
attrs='''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::unwind(65)]
'''
rows=[]
for kind in ['raw','weight','line','inverse']:
 for neg in [False,True]:
  name='NBZ_'+kind+'_window'+('_negative' if neg else '')
  s+=attrs+'fn '+name+'(){NBZ_'+kind+'_case('+str(neg).lower()+');}\n'
  rows.append(dict(harness='verifier::candidate::NBZ_windows::'+name,negative=neg,kind=kind))
Path('/tmp/NBZ_windows_generated.rs').write_text(s)
(E/'NBZ_windows.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBZ_windows.rs')))
(E/'NBZ_WINDOW_PLAN.json').write_text(json.dumps(rows,indent=2)+'\n')
