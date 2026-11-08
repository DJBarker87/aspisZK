# Stage 2: TGB-1b OPEN

NNP_ResumeHeader.resume/okHeader/okHeader_any compile at NNP_L003, standard
axioms only. They restrict the required oracle agreement to the TWO actual
header singleton replies. The third, checksum, call is preserved inside the
successful resume; its model value is unnecessary to the decoded header.
The proof reuses merged NNH_064EnvHeader.resume, importing the original native
proof rather than duplicating it. All LIBW statements remain unchanged.

Exact remaining fact at each reached Env/input:
LIBB_HashModel.H env (protocol proof) = LIBB_PartitionEnv.H env (protocol proof)
and the analogous equality at public bytes. These are HeaderAgreement.
The left side reads env.sha256 [host message]; the right side reads env.sha256
(LIBB_C04Partition.partition (host message)), a three-element list. No universal
repartition-invariance premise is available. LIBB_Tx2Auth.native assumes the
original four input clauses, the native invocation, Bound064 (reservation
representation), and TraceOf; it does not supply this hash equality. HostRep
and HostRepAny identify an observation with that invocation; neither constrains
env.sha256 across partitions. Thus the conditional header theorem is NOT an
unconditional discharge of okHeader or a proof of implication from the canonical
law's existing hypotheses. TGB-1b remains an owner-visible obligation against
TOP:G1b/TOP:G2. Do not install HeaderAgreement as new host trust.

The separate-hash route already exists in merged NNH_064EnvHeader.native:
resume headers use LIBB_HashModel.H while C04 uses LIBB_PartitionEnv.H. Using
that route at the final Sig requires the integration owner's readerHeader
interpretation, rather than silently changing LIBW's existing theorem statement.

NNP_L002 failed only on RSL named length constants; NNP_L003 unfolds those
constants in the proof, with the same statement. NNP_L004/L005 attempted a
state-valued partition-sensitive counterexample; both failed elaboration
(record projection simplification, then an unavailable simp lemma). That shape
is retired after two failures, no theorem credit; its last source is .retired
and failed snapshots remain in receipts. No failed shape was rerun unchanged.

Target not yet established.
