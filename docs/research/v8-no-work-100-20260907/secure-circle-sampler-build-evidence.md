# Secure-circle sampler checkpoint evidence

Status: all four checkpoint leaves are kernel-checked, with 33
standard-only axiom audits. Fourteen attempts are retained: four green
results and ten failed diagnostics. The prospective `OrdinaryPrefixMass`
continuation is excluded. No actual raw-tape/source sampling probability
is claimed.

The new [auditor](experiments/secure-circle-sampler-audit.py),
[transfer receipt](secure-circle-sampler-transfer.json), and
[evidence record](secure-circle-sampler-evidence.json) are separate from
all committed higher-Y and quadratic checkpoints. Earlier sources,
outputs, and checkpoint metadata are checked as inherited bytes, not
recompiled and not credited as new theorem audits.

## Checked interfaces and remaining boundary

- `SecureCircleParameterDomain` establishes that the literal decoded map
  accepts exactly the parameters outside CM31, with cardinality P⁴−P².
  The two singular parameters are already inside CM31, not an additional
  subtraction. [Domain review](secure-circle-parameter-domain-review.md).
- `DistinctCircleDecoder` proves the deterministic nested retry control
  flow: inner failure aborts, only a successful duplicate retries, and
  successful output is distinct and insensitive to an unread suffix.
- `BoundedRetryKernel` proves a conditional, history-dependent mass
  recursion. Its one-step hit and successful-rejection laws are premises
  at every history; failure contributes zero and is never retried.
  [Decoder/kernel review](secure-circle-retry-review.md).
- `SecureCircleParameterInverse` recovers the parameter from actual
  successful returned coordinate bytes, and proves that equality of two
  successful points is equivalent to equality of their parameter bytes.
  Its run premises supply the canonical decoding and nonzero denominator;
  these are not extra caller correspondence assumptions.
  [Inverse review](secure-circle-parameter-inverse-review.md).

These do not yet identify that mass recursion with the actual finite raw
tape after stopping prefixes and intervening answer absorption. They
do not prove fresh independent draws from transcript labels, the joint
distinct-circle-point law, or a new global OOD term. The existing OOD
indicator and complementary accepted mass remain explicit.

## Provenance and resource contract

New source parent: `ce36c58168987142d3f07e5d8cba00fb7b1dd05b`.
Inherited runner/overlay parent: `289d7356c78a4cd493fe61a54f9548f2a0c11298`.
Borrowed V7: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
Lean 4.32.0: `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.

Every retained attempt records the literal command and actual cgroup
settings: MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0,
CPUQuota 200%, Lean `-j1 -M9500`. The receipt maps each attempted source
to its immutable runner-created snapshot. Green outputs must match
the current source and the successful pre/post import manifest.
Native package caches remain a declared pinned-revision boundary;
they are not rebuilt or fully replayed by this audit.

Remote transport is Tailscale `dombarker@100.108.41.90`, with
`BatchMode=yes`, `ConnectTimeout=10`, `StrictHostKeyChecking=yes`, and
`HostKeyAlias=nuc.local`. The alias selects a host key, not a DNS route.

The read-only semantic-transcript cache preflight found an exact V7
source/native artifact pair, but its full import would introduce 31
additional modules and 12 differing native boundary artifact versions.
No such import or manifest change was made. The inverse leaf instead
reuses only the relevant codec proof bodies from the pinned V7 source.

The four reused codec declarations were independently compared against
the exact borrowed git blob, including their proof bodies: they are
identical modulo whitespace. This does not award additional audits
beyond the inverse leaf's sixteen.

The separate [ordinary-law interface](sampler-ordinary-law-interface.md)
and [cache preflight](secure-circle-sampler-cache-preflight.json) concern
the next continuation only. FlatRouting's closure would add 38 modules,
reaching 18 existing pinned boundaries, with 12 differing native olean
versions. All 18 overlay boundary pairs match the retained manifest.
The native `V7Tag73TranscriptSchedule` source has drifted
(`1e9ebd3c…`); the frozen borrowed/overlay source (`a55c187d…`), not the
mutable native pathname, is the valid retained source for its unchanged
olean. No extra module was copied, mixed, imported or compiled.

## Final census

| Leaf | Green attempt | Wall seconds | Peak RSS KiB | Audits |
|---|---|---:|---:|---:|
| SecureCircleParameterDomain | v2 | 3.30 | 6,692,052 | 9 |
| DistinctCircleDecoder | v2 | 2.92 | 6,674,044 | 4 |
| BoundedRetryKernel | v2 | 2.97 | 6,701,840 | 4 |
| SecureCircleParameterInverse | v8 | 3.43 | 6,842,872 | 16 |

Every attempt used zero swaps. Domain v1 omitted a named definition from
the encoded wrapper's restricted simplifier; Decoder v1 lacked a decision
instance for byte-function equality; Kernel v1 lacked its final section
terminator. The inverse's seven failed attempts isolate syntax/decoder
rewrite and nested native quadratic-instance conversion issues, including
the retained v4 explicit-type diagnostic. The final inverse uses small
coordinate subtraction and bounded congruence conversion, without a cap
increase. See its review for each failed attempt's exact replacement.

All fourteen immutable source snapshots, logs and per-run manifests are
retained. The transfer receipt resolves 103 exact artifact versions with
zero unmapped entries. The evidence records every source/output SHA-256,
literal command, exit, wall time, peak RSS, swap count, source snapshot,
import-manifest hash, and all 33 green declaration axiom lists. Failed
attempts (including any downstream `sorryAx` diagnostics) receive no
successful-file or axiom credit.

## Verification

The final check is read-only and rejects changed source/output bytes,
missing attempts, unexpected axioms, resource-contract discrepancies or
a changed record. It does not run Lean, contact the NUC, or replay an
earlier theorem suite:

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/secure-circle-sampler-audit.py --check-recorded
```

The [open ledger](secure-circle-open-ledger.json) retains null global
charges. Its proposed distinct-root pair expression is not substituted
into the causal bound by this checkpoint.
