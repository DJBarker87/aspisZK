import RPx_PreAccept
/- L166 scoping: inspect actual declarations; no concrete refinement instance asserted. -/
set_option pp.proofs false
#check @AspisR1.RPx_PreAccept.complete
#print axioms AspisR1.RPx_PreAccept.complete
#check @AspisR1.RPx_PreAccept.guard_reject
#print axioms AspisR1.RPx_PreAccept.guard_reject
#check @AspisR1.RPx_PreAccept.parse_reject
#print axioms AspisR1.RPx_PreAccept.parse_reject
