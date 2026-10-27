# Precise residuals

V403 is a P obligation. No native fact is added to T. No unconditional
canonicality claim applies to arbitrary `M31(pub u32)` values.

P_installed: the frozen deployed records execution (tools/r1-builder-reference/
pv_runjoin12_shipped.rs on codex/pv-runjoin-20261026; original
crates/aspis-r1-cost-probe/src/records.rs) agrees with the extracted caller,
including its ExternalFuns dictionary and successful/failing semantic updates.
The records P6 candidate is not a proof of this statement.

P_oracle: in every invocation of the installed semantic oracle inside
host_sumcheck::prove_sumcheck (host_sumcheck.rs:58), a successful returned QM31
has each of its four underlying u32 representatives <2147483647. The oracle
instance is built by host_semantic, not universally quantified arbitrary closures.
A proof on a chosen dictionary must expose its precise selected entries.

P_challenge_update: every successful SemanticTranscript::semantic row 15..24
(r1_wire.rs:248..253) returns the qm31_sample of the successful sample_block
return and updates exactly the extracted transcript state. Hash output is
arbitrary; canonicality needs no entropy assumption.

P_op121_canonical_source: for every polynomial : [QM31;28] and challenge : QM31
with all 112 coefficient limbs and four challenge limbs <P, the actual shipped
`state_only_sumcheck::evaluate_state_only_polynomial` (state_only_sumcheck.rs:
160..187) has the same complete success/failure Result and output as its
accepted extracted definition (or an owned index-loop reference with a proved
structural/Lean link to this body). To use a Horner reference additionally prove
its decoded result equals Σ i=0..27 decode(c[i])*decode(challenge)^i, and prove
canonical representatives make the decoded equality injective. Radix-four block
indexing, specialized square, qm31_sum_products3 and PreparedQm31Multiplier must
be included. Domain canonicality alone does not establish this source law.

Direct extraction's loop/closure obstruction (D251/D257) does not authorize
changing op121. Route (ii) remains a candidate requiring lead adoption and the
usual shipped association gates. No source rewrite is made here.
