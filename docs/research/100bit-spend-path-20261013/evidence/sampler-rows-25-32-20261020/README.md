# Focused sampler suffix proof packet

`manifest.json` selects the successful final source checks. Each attempt has
its exact command/search path, source SHA-256, receipt, complete Lean output
and `/usr/bin/time -l` output. Interrupted waiting attempts explicitly record
that compilation did not start. Import failures and proof drafts are retained.

The launch revision was f2c084bc8. `source_content_revision` identifies the
commit containing the byte-identical checked final sources (verified by source
SHA), rather than claiming the uncommitted source existed at the launch HEAD.
Direct-import object hashes and their fingerprint were captured postflight;
the worker did not overwrite shared objects. Own suffix objects were finalized
before dependent successful bridge checks. There are no committed objects.

Final targets: RawSamplerSuffixCorrespondence, RawSamplerSuffixSourceFrames,
RawSamplerSuffixSourceBridge, RawDeployedTranscriptFormat. These yield 20
standard-only theorem audits. RRInitialFullRowsScanFacts was rebuilt unchanged
into the private object directory as one missing dependency (two more audits).

This packet is local conditional evidence. It is not a full frozen-manifest
replay, current-CU source re-pin, binary Merkle acceptance bridge, or proof of
the complete deployed acceptance-to-Checks implication. See the per-row report
in ../../design/SAMPLER-ROWS-25-32-20261020.md.
