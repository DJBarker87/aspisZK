# Stub/domain audit

No field multiplication operation is stubbed or proved in Kani. There is no
field multiplication stub/theorem/domain table to instantiate. No SHA, PDA,
decoder, allocator or account-borrow implementation replacement is used.

Copy replacements are exactly KMX_copy_stubs.patch
bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67,
actual stub body ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138.
Program crate uses the very same root file via a cfg-only module path; no copy
stub was rewritten. Value laws reused: KMX_CopyMeaning.loop_spec/copy_frame,
append_spec/realloc_prefix, through the existing NBU/NBX proof chain. Pointer
validity, non-overlap, length, initialized-value and allocation admissions stay
explicit. Each credited copy-dependent component has a matching single-failure
inverse in the exact same configuration (see NCF_BOX_AUDIT and NCF_AUDIT).

Verified Bool contracts: native op25–28 inherited NCC body proofs plus NCF
individual inverse/use controls; op29/30 K002–009 paired with
NCF_EntryContract.op29_exact/op30_exact (all valid typed entries/every U64 slot).
These are local consumers, not SDK authentication closure.

Policy Result contracts: K058/K065 positive; K059/K066 invalid postcondition
controls. K061/K067 are PROVISIONAL; no native bridge credit. Their extra ghost
pointer precondition is a domain finding. No extraction component relies on
this conditional contract. K062/K068 correctly fail their caller assertions but
do not repair the invalid callee controls. All eight actual error enum variants
are generated in cfg-only harness input code; no foreign Result/Ref/guard value
is forged from bytes.

Input-only weak modifies contract: K026 CAR failure, K027 invalid control,
K028 compiler ICE. No arbitrary_long candidate was run and no production
operation was replaced by that helper. It has no verification credit.
