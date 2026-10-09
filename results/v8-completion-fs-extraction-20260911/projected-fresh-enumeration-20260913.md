# Projected fresh-enumeration leaf (2026-09-13)

## Scope

`FSV8ProjectedFreshEnumeration.lean` proves a deterministic projection lemma.
Given a literal V7 entry-history prefix, verifier provenance for every record
in the chronological suffix, and a fresh FS event in the mapped suffix, it:

- recovers a literal source record with the same input and answer;
- proves that record has origin `fresh` (so cached/programmed records are not
  silently counted);
- preserves the separately supplied verifier actor fact; and
- places the exact input/answer pair in `freshQueryEnumeration`.

This is not a probability, freshness-law, or source-run coupling theorem.  It
consumes the chronological prefix and verifier-provenance facts that the whole
source factorisation must construct.

## Source

- checkout revision before this uncommitted leaf:
  `3e2a3a845e24d3253e4635d4056cdcb6e8e9dbbf`
- file SHA-256:
  `db04488d9d1208ed078c7e94626568196cae87357c012ff8781a939c42cb0869`
- Lean: pinned `4.32.0` binary at
  `/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean`

## Focused replay

The final run used the existing pinned dependency cache and a user systemd
scope with `MemoryHigh=7500M`, `MemoryMax=8G`, and `MemorySwapMax=0`:

```text
unit: v8-projected-fresh-enum4-432-20260913.service
exit: 0
wall: 2.51 s
user: 1.68 s
system: 0.83 s
maximum RSS (/usr/bin/time): 6,676,852 KiB
swaps: 0
```

The systemd summary reported a non-representative 512 KiB memory peak; the
`/usr/bin/time -v` child-process RSS above is the recorded resource figure.

Two earlier focused attempts failed during proof plumbing (prefix equality
orientation and mapped-list length alignment).  They were corrected before
the successful run; neither produced retained declarations.

## Axiom audit

Both promoted theorems report exactly:

```text
[propext, Quot.sound]
```

There is no `sorryAx` or custom axiom in the retained leaf.

