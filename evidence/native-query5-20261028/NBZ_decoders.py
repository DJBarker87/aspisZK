from pathlib import Path
import difflib,json
E=Path(__file__).resolve().parent
s=Path('/tmp/NBZ_decoders.rs').read_text()
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
for name,case,arg in [('base_ok','base',False),('base_reject','base',True),('tail_main','tail',False),('tail_extended','tail',True),('values_ok','values',False),('values_reject','values',True)]:
 for neg in [False,True]:
  h='NBZ_'+name+('_negative' if neg else '')
  s+=attrs+'fn '+h+'(){NBZ_'+case+'_case('+str(arg).lower()+','+str(neg).lower()+');}\n'
  rows.append(dict(harness='verifier::candidate::NBZ_decoders::'+h,case=name,negative=neg))
Path('/tmp/NBZ_decoders_generated.rs').write_text(s)
(E/'NBZ_decoders.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBZ_decoders.rs')))
(E/'NBZ_DECODER_PLAN.json').write_text(json.dumps(rows,indent=2)+'\n')
