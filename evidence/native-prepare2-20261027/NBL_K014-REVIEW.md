K013 did not compile (assume(false) is unit); corrected K014 exceeded its
unchanged90s CBMC timeout: exit1,94.363230377s,1734008KiB,swap0.
The large position span carried the seed, four scalar payload/state vectors,
query, rho, scratch overwrite and claim inputs together. It was not rerun.
K015 isolates the source suffix AFTER the opening (same position/carrier
boundary as K008's query entry), preserving query/rho/powers/claim routing.
K015 passes807 checks and one reachability cover at59.777600154s,2922924KiB.
No cap/timeout increase, no field multiplication, no unchanged rerun.
Own solver cleanup is retained in NBL_K014-cleanup.json.
