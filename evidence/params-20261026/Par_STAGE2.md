# Stage 2: accepted-pair specialisation and constructed public carrier

Par_NativePair.accepted_pair has no M,Cv,N,p binders. It instantiates the
original DrvC accepted-pair theorem at Par_Parameters.deployed, preserving
all other native/source/runtime/trust arguments. Same f,s,cuts,decoded, saved
and post1/history are retained; no independent successful run is supplied.
It constructs an exact Input from f.pub/f.proof, with public tag2, exports
public length1880 and the bound 75+1880≤131072, and derives acceptance and
exclusion of reject-everything under the ORIGINAL history/P2prime premises.
No caller initFits or public-size proof is added. Its generic conclusion's
arbitrary Input is specialised to this source-associated Input.

Source chain: owned stage1 :390 calls decode_public_statement_box on borrowed
public_data; adapter :237 delegates to decode_pool_v1_pair_forest_terminal_statement_v1;
pair_forest_terminal.rs :403 rejects wrong length, and :822 asserts size1880.
DrvC_PublicCarrier.public_length uses the installed decoder accepted_inverse
on THESE cuts.decode; Par_Public.accepted_public_bound preserves this chain.
This reuses the existing source/codec refinement and does not newly prove the
native decoder or runtime boundary. The bound proof uses lengths, not concrete
public-byte evaluation. Tag2 is the existing selected public-statement tag.

Validation: Par_002 failed due to missing namespace open for bytesOf; its
error-generated sorryAx audits are EXCLUDED. Source corrected by opening the
original MultiproofConeCanonical namespace. Par_004 passed (1.962998802s,
5268968KiB, swap0), Par_003 passed (2.050379293s,5274268KiB,swap0). All accepted
new theorems print only propext/Classical.choice/Quot.sound. No timeout/OOM.
Budget 4/40 actual compiles,0/0 Kani. Config numbering reflects sequential
proof dependencies (004 public correction precedes003 native consumer).

Next: compose this parameter-free native result with the ORIGINAL installed
DrvC headline, keeping raw L157 and StoredCarrierBinding L159 unchanged.
