# Parsed inactive bytes to current claim field interpretation

PROVED: `parser_carrier_decode_same` shows the literal eight-limb carrier map from the retained parser output to preparation/current claim arithmetic has exactly the old checked decoder's mathematical WideExact interpretation. `parsed_inactive_decodes` therefore derives the current claim field value directly from successful parsing of the same fixed32-byte input, via the existing strict byte-codec theorem. No independently supplied canonicality or decoded-value equality is assumed.

This reuses the existing R1SourceWideExactCodec.successful_parse_decodes owner, source61cf8c…/object8c5c6e…, rather than re-proving/replaying the parser or field representation. The new theorem is representation plumbing for the S1 inactive value; no Merkle-path, tree-format or commitment-model work is introduced.

OPEN: installation in the actual transaction/adapter, cached-claim/P6 correspondence, authenticated proof-buffer/checkpoint binding, runtime/artifact and global100-bit closure. This does not authenticate arbitrary bytes or prove complete statement correspondence. The per-attempt versus per-query issue in the new lead bound remains separate and unresolved; no query-normalised result is substituted for the goal.

One focused local Lean4.32 -j1 -M4400 target passed,17.988s,aggregate3736076288B/process3758440448B,zero swaps; both audits standard axioms only. Exact warm cache reused, no dependency build or unchanged replay. Source/object/compiler/import/command/resource pins retained; no binaries or production/CU/artifact changes.
