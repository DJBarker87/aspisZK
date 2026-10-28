# Selected-View model adapter and native Parse prefix

NBL_ViewOffsets (L084) reuses unchanged AuS1_Offsets from coherent SInt2 and
extends its last two offsets. Existing objects were discovered read-only,
not rebuilt or modified. L083's attempted decidability path was rejected.

NBL_SlicePort (L087) reuses the checked generic slice-range laws, proving exact
bytes/length and the zero-length query slice. L085/L086 needed explicit scalar
zero and equality composition across the wrapper. NBL_ArrayPort (L091)
proves the generic slice-array conversion using the actual Usize len guard;
L089/L090's mistaken Nat guard attempts are rejected.

NBL_ViewProduct (L095) composes the full selected nominal View/Parse Result,
same proof ranges/root/pass-through fields, on a local inactive parse.
L088/L092/L093 hit unchanged recursion limit during elaboration of a concrete
range-length coercion. Reuse the root array's existing property instead of
re-normalizing that proof. L094 fixed final branch reductions; caps/limits
unchanged. NBL_ViewNatural (L097) discharges that inactive parse using the
EXISTING all-input strict UnrolledWideParserRefinement, yielding the whole
model Result from original bytes. No selected successful view or inactive
value is a premise. L096 qualified arrayBytes32.

NBL_ViewDomains (L099) derives semantic/y1 pass-through, S2,224/224/2048 payload
sizes, Some root and its exact32 source bytes from SAME producer and frozen
proof length. L098 encountered an ambient namespace alias to XRn; it did NOT
compile or receive credit. L099 fully qualifies the selected function/carrier.
Accepted model adapters target AspisR1SelectedWideViewV1, not XRn stand-ins.

These are checked model adapters/caller-domain ingredients, not an independently
claimed whole native prepare bridge. Native producer/trace obligations are
named in NBL_OPEN_DEPENDENCIES.md. Standard axioms only.
