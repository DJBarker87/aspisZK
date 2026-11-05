# NHB stubs and domains

No field multiplication is reached or stubbed. No function-pointer/Option<fn>
value is used. No writable static is used. No stub_verified call is credited yet.

The prescribed KMX patch is installed verbatim in the scratch tree:
SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
KMX file hashes are checked inside EVERY Kani gate before metadata and Kani.
The annotation targets core::ptr::copy_nonoverlapping with KMX_copy_nonoverlapping.
No private replacement copy stub is introduced. Negative controls must fail in
the identical KMX configuration before copy-dependent native credit.

NHB_contains_0..22 contracts specialize the native slice bound to the length
stated by each requires(n==L). All22 words and x are arbitrary. The domain
partition is exactly0..22; a caller must prove its len<=22 and select its SAME
length. The reference disjunction reads exactly indices0..L-1. Its Lean value
law is NHB_Membership.reference_eq / prefix_membership (L004). These are model
laws over the SAME prefix, not claims that all native contracts passed.
Native membership contracts are local callee laws only; root state/frame,
iterator and chronological physical trace association remain OPEN.
