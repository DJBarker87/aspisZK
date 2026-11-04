# Decoder and accepted return-data model association

NFR_RawInverse.raw_inverse : NFO_Final.RawInverse is proved, with no
codec/inverse premise. NFR_RawInverse.accepted_codec applies
NFO_Final.codec_iff_raw and discharges AcceptedCodec. The proof uses the
actual accepted raw decoder on the SAME slice, derives header and field frames,
uses the CLOSED digest and afterstate accepted inverses, and telescopes the
serializer's layout over disjoint slices. No 792-byte concrete normalization.
The original quantifiers and carriers are retained.

B001 proves child provenance/error-map laws. B005 proves totality of the
canonical result validator without importing the duplicate S2K owner forest.
B009 proves raw accepted frames. B011 proves the inverse and codec. Failed
B002 imported an incoherent NBN forest, rejected before declarations; that
import was removed. B003/B006/B007/B008 expose missing constant bounds or
header/scalar facts; B004 missed map-error totality; B010 had an underspecified
simp-lemma instantiation. Failed diagnostic sorryAx is never imported/credited.

B012 proves NFR_ExtractedDecode.probe and .oracle: E001's sixteen selected
closure/decoder definitions, on the canonical carrier/child owners with monadic
constant slots retained, equal the already checked NFO raw body and oracle
substitution. NFR_B_generate_extraction.py --check reproduces the exact port.
NFR_B_TEMPLATE_AUDIT.json maps all 19 TEXT-ONLY external declarations,
including which are top-level slots and which occur only in CLOSED children.
The external template is never compiled/imported. This is a body/owner
association under the existing child/Std/extraction interpretation, not a new
runtime implementation theorem or removal of P6/extraction trust.

B013 compiles NFR_PoolReturnData.association: for the SAME context/program,
the new nonempty RuntimeReturnData row, valid statement, and accepted Pool read,
derive emitted bytes, SAME decoded typed value, saved bytes, its exact
serialization and local clear/invoke/read/decode events. There is no codec or
decoder-association premise. Acceptance is the event analysed, not a new trust
row. This accepted-run theorem alone does not establish a reachable accepting
native execution or complete Pool settlement.

Every new theorem printed only propext, Classical.choice and Quot.sound (or a
subset). Exact sources, source revision, commands, dependency/Aeneas pins,
exit/time/RSS/swap/cgroup limits and complete print output are in each B receipt.
B011: exit0, 2.4904 s, 5397404 KiB, swap0.
B012: exit0, 3.1612 s, 5405960 KiB, swap0.
B013: exit0, 2.6570 s, 5395728 KiB, swap0.
All are focused cached-cohort results, not a cold release replay.

No shipped source, existing proof owner, artifact, wallet or key was changed.
No Kani/extraction run is charged to B; E001 is reused. Native account/context,
carrier and settlement certificates are separate A/C obligations. The joint
non-vacuity and cold coherent release gates remain separate.

Continuation B035-B037: the final forward decode proof now compiles.
B035 replaced elaboration-permissive rewrites with exact rewrites, removing the
recursion-depth obstruction, and isolated the remaining afterstate encoded-slice
numeral proof mismatch. B036 uses the named afterstate roundtrip after explicitly
unfolding only its encoded-slice wrapper: forward/emitted/decoder_association
all compile with standard axioms. This is a symbolic composition of the closed
header, field-window, canonical-digest and afterstate laws, not wire-buffer
normalization. B037 compiles the current NFR_PoolReturnData association, which
derives accepting decoder/read output for every valid emitted statement; no
independent accepted-read, inverse or decoder-association premise remains.
The accepted_association root is retained too. This mathematical result does
not establish a complete native Pool execution or a reachable two-transaction
witness; A/C native caller and joint non-vacuity gates remain separate.

B036: exit0, 2.5121 s, 5328848 KiB, swap0.
B037: exit0, 2.6278 s, 5316304 KiB, swap0.
