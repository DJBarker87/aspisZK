# Stubs and caller-established domains

No field multiplication or function-pointer-dependent value is reached.
No writable static or new runtime trust row is used.

The EXACT prescribed KMX_copy_stubs.patch is applied in the scratch tree;
sha256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
Every Kani gate checks its installed source pins, frozen offline graph and lock.
The only copy stub is core::ptr::copy_nonoverlapping -> the prescribed
crate::KMX_stubs::KMX_copy_nonoverlapping. The native windows have matched
failing controls in the identical KMX configuration, including exact byte0
corruptions K031/K054. No private copy stub is introduced.

| Call-site stub | Native contracts and controls | Value law / domain |
|---|---|---|
| K046/K047 stub_verified NHB_contains_0..6 | K003/004 through K015/016 | NHB_Membership.reference_eq and prefix_membership, same active prefix; exact n=0..6, arbitrary22 u32 words and x |
| K046/K047 stub_verified NHB_contains_7..10 | K020/021 through K026/027 | same laws; exact n=7..10, owned22 arbitrary u32 words and x |
| K053/K054 NHB_member_logged | intentionally returns the supplied arbitrary Bool; no native predicate association | CONDITIONAL ONLY; exact argument/call-count/frame log, no membership-value credit |

Bool is the admitted pure scalar interface; no new non-Bool contract shape is
used for stub_verified. Each low caller establishes the selected helper's exact
length precondition; no timed-out helper is substituted. Canonicality,
inactive-zero and bounds for the caller are proved in NHB_Canonical,
NHB_Inactive and NHB_Domains. NHB_Prefix.member associates the SAME active
survivor prefix. NHB_Observation.ghost_inputs establishes pre-observation
availability, not desired poststate equality.

K055/K056 and any later successful length-specialized contracts have an
expected Bool parameter uniquely constrained to the scalar prefix predicate;
NHB_Membership.prefix_membership/NHB_Prefix.member give its model value law.
They are local contracts, not used as a stub in a credited full-domain caller.
Final checked cases are listed in NHB_MEMBERSHIP_CALLEES.json. Speculative
unlaunched full dispatch/reference source files carry no native credit.
