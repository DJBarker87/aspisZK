# S6 native afterstate encoder / reference decoder byte law — 2026-10-23

## Exact enclosing claim

`AspisS6NativeAfterstateEncoderReuse.accepted_roundtrip` proves:

```lean
∀ (bytes : Slice U8) (a : ReferenceAfterstate) (encoded : Array U8 688#usize),
  decode_reference bytes = ok (RustOk a) →
  encode_native (native a) = ok (RustOk encoded) →
  encoded.val = bytes.val
```

These are the two concrete success conditions; no encoder-byte interpretation,
child encoder success, canonicality, validator success or iterator-output
premise remains. `decode_reference` is the complete concrete
`AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1`.
`encode_native` is the original iterator-based
`AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1`.
The file states those functions in full, without abstract operation arguments.
The `native` function constructs the original full native afterstate with the
same next index, full root digest, and complete twenty-digest frontier. It is
not a reduced public projection or an opaque replacement.

The decoder contract contributes the complete header, index and 21 digest
frames plus actual validation result. The native encoder success is used with
S2K's checked `status_exact` to derive its actual validator success. The
existing `AfterstateEncoding.encode_exact`, `AfterstateBytes.loop_exact` and
`DigestBytes.exact` then fix the actual native output. New symbolic list/write
lemmas identify that output with the exact decoded frames; the source iterator
and digest loops are reused, not replaced or reproved.

The two-success form matches the local byte-equality shape needed by
`FullForestAcceptedRoundtrip`. This packet does **not** instantiate that full
1,880-byte law. In particular its decoder is still the full concrete reference,
not the legacy native decoder or the current SDK's op47 installation. That
source/caller transport remains an explicit separate obligation. The theorem's
full statement must be used when assessing closure; its short name is not a
claim that the complete native codec is closed.

## TOTAL versus accepted-only

The reference decoder's preceding TOTAL theorem still covers arbitrary input
slices and every source rejection path. `frontier_fold_contents` is a symbolic
pure-fold identity on arbitrary raw rows and initialized buffers; it does not
assume canonical digests. `native_afterstate_contents` identifies every byte of
S2K's actual encoder payload for every native record. The final byte law is
ACCEPTED-ONLY with both concrete calls retained. This packet does not establish
totality of the original native validator or the complete SDK/runtime path.

## Necessary candidate naming repair

The combined native/reference import initially failed because Aeneas emitted
both enum instances as the same root name
`instDiscriminantPoolV1TransitionKindU8` for distinct full native enum types.
The isolated `S6NamedDiscriminantV1` adapter reuses Aeneas's original
`generateReadDiscriminantCmds` reader generator with the same closed u8 values
`[1,2]`; only its instance declaration has a type-qualified name. It adapts the
existing import-union prototype. Its own attribute registry name is also
unique, avoiding a collision with that prototype.

The enum declaration, constructors, reader and 1/2 values are unchanged.
`S6TransitionDiscriminantMeaningV1.exact` has the same quantified statement and
checked proof before and after the naming change. The corrected attribute
registry name produces a byte-identical type object to the first named variant.
The materializer now emits this repair permanently and its `--check` passes.
No Rust, frozen production verifier, SDK, security contract or wire byte changed.
No production adoption decision is requested. The Lean candidate object/import
pins change, so all previously accepted descendants of this type owner were
recompiled in dependency order and their focused packet selections re-pinned.
This is a justified affected-dependency replay after a source/library naming
change, not an unchanged frozen-manifest replay.

## Existing proof and cache reuse

The NUC already held S2K's exact encoder proof. Discovery found 19 missing local
objects and 43 different common dependency objects. The remote cache was used
to locate the proof and its sources; it is not credited as a coherent mixed
release closure. All 19 missing proof sources were copied verbatim and compiled
against the selected local dependencies. All 19 match the observed research
source files byte-for-byte; exact paths/hashes are in
`s6-s2k-source-reuse/provenance.json`. Source-only copies are retained in its
`sources/` directory. No S2 owner's source or live worktree was modified.

The imported native source module is the existing extracted
`AspisR1TerminalDecoder.Funs`; its selected object is included in the transitive
pins. Statement/core-field compatibility with the current observed research
source remains as recorded in the preceding packet. This does not identify the
legacy extraction with the current release SDK merely by function name. Full
current source, runtime, call-site and release-artifact transport remains open.

## Validation

Every focused Lean invocation used the atomic local lock and `-j1 -M4400` with
warm dependencies. No heavy build was launched on the NUC. The local runner now
also accepts an explicit in-worktree source directory so verbatim proof reuse
can be checked without copying other owners' modules into the candidate tree.
The import-pin tool resolves the exact source path from each receipt.

The selected packet contains 87 successfully compiled targets and 210 standard-or-empty
axioms reports. Maximum selected RSS was 3299622912 bytes; every selected run exited 0
and used zero swap. Summed selected target wall time was 465.538 seconds. The final byte-law
file checked in 14.446 seconds at 3254583296 bytes RSS, zero swap. Its three
axioms reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

Exact source revisions/hashes, tool hashes, commands, direct imports, wall/RSS,
swap and audits are retained per attempt. `s6-native-afterstate-byte-law-targets.json`
selects the accepted attempts and records source paths. The transitive object
hashes are in `s6-native-afterstate-byte-law-import-pins.json`; script hashes are
in `s6-native-afterstate-byte-law-tool-pins.json`. No binaries are distributed.
Earlier failed imports and proof elaborations are retained as excluded
diagnostics; no failed `sorryAx` result is installed. Resource ceilings were
not raised. Prior selected receipts are archived in
`s6-native-afterstate-repin-prior-accepted.json` before refreshing the six
focused packet selections.

## Exact remaining work and next target

First close the native decoder side of this 688-byte law: derive the same full
frames from the actual extracted native decoder, with native source/caller
pins, rather than assuming a reference/native decoder association. Reuse the
existing scanner, canonicality and parsing facts and original native iterator
proofs. Then compose snapshot800, transition1520 and forest1880, including both
payment variants and all reserved/header bytes. The actual current full public
serializer/first-decoded ports must still preserve the full statement, public
and proof slices, release observer None, errors, state/ownership, allocations,
abort prefixes and ordered reads. S1 preparation/gamma scratch/challenge and
resumed-powers caller ports also remain. S2 is externally owned. The 100-bit
per-attempt target is not yet established.


## Addendum: native decoder gap discharged

`S6-NATIVE-AFTERSTATE-CODEC-20261023.md` supersedes this packet's remaining
688-byte native-decoder gap. The original native decoder and encoder are now
TOTAL, and actual native decode success alone derives successful native encoding
and exact input-byte recovery. The same native full carrier is used directly;
no reference-decoder association remains in that theorem. Full forest/SDK/caller
transport remains open as before.
