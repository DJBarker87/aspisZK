from pathlib import Path
import difflib,json
E=Path(__file__).resolve().parent
s=Path('/tmp/NBZ_dictionary.rs').read_text()
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
for name,call in [('embed_base','NBZ_embed_case(true,'),('embed_q','NBZ_embed_case(false,'),('comparison','NBZ_comparison_case('),('inverse','NBZ_inverse_case('),('line','NBZ_line_case(')]:
 for neg in [False,True]:
  h='NBZ_'+name+('_negative' if neg else '')
  s+=attrs+'fn '+h+'(){'+call+str(neg).lower()+');}\n'
  rows.append(dict(harness='verifier::candidate::NBZ_dictionary::'+h,case=name,negative=neg))
Path('/tmp/NBZ_dictionary_generated.rs').write_text(s)
(E/'NBZ_dictionary.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBZ_dictionary.rs')))
(E/'NBZ_DICTIONARY_PLAN.json').write_text(json.dumps(rows,indent=2)+'\n')
