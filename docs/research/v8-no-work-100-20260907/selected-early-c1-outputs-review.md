# Same early-C1 table: strict amounts and output-note openings

Status: **GREEN**, focused NUC v2, all nine audits using only `propext`,
`Classical.choice`, and `Quot.sound` (some use a subset). The original source
bytes, including the historical “Source-review draft” header, are frozen;
the successful check required a missing-cache repair, not a proof change.

## New deterministic bridge

The new `member_outputs_or_copy_collision` endpoint continues from the
green `SelectedEarlyC1Amounts` table and `AmountFacts`. It constructs the
literal decoded recipient/change notes, proves their strict positive
30-bit values and conservation with input row44, and binds their modeled
note hashes to the independently supplied public commitments. The existing
lambda/chi collision alternative remains explicit.

Two real interfaces are discharged, rather than assumed:

1. **Four note carry links.** `weighted_aliases_supply_output_carries`
   derives all 64 scalar carry residuals from the actual selected weighted
   aliases. The four existing source links are:

   | Link index | Producer | Consumer | Transfer weight |
   | --- | --- | --- | --- |
   | 3 | row443, all 16 columns | row448 | 1 |
   | 4 | row459, all 16 columns | row464 | 1 |
   | 5 | row491, all 16 columns | row496 | 1 |
   | 6 | row507, all 16 columns | row512 | 1 |

   Their actual tuple pattern is width16/start0/offset0. A four-case pure
   metadata certificate identifies the registry entries; field-valued
   tables are not enumerated. The existing transfer-weight lemma supplies
   the unit weights. Equality is projected to the base coordinate; no
   claim that arbitrary QM31 products survive that projection is used.

2. **Canonical raw decoding.** `rawSemanticTable` is the canonical `.val`
   representative of the same `semanticTable`. `raw_canonical` proves its
   values are below the M31 modulus, and `rawTable_exact` proves their
   field re-encoding equals the original table everywhere. Existing
   `both_raw_transfer_output_openings` therefore applies without a supplied
   canonical-decoder-success premise or a different expected table.

`output_residuals_from_selected_copy` constructs each existing
`OutputResiduals` record, supplying its previously assumed `carry` field.
The source pair-round, initial-state and six tail-zero checks per output
remain explicit in `OutputSemanticChecks`. Actual asset and commitment
binding residuals also remain explicit. Owner/amount/split-salt positions
are the existing block27 and block30 decoder definitions, including amounts
at rows460/508 and final commitments at rows475/523.

`decoded_output_value` identifies these raw note values with the exact
recipient/change `decodedValue` entries used by the earlier amount theorem.
Consequently `AmountFacts` supplies strictness, conservation and `u32`
output-sum safety for the notes whose openings are actually proved—not
merely for unrelated field amounts.

## Premises and limits

The endpoint retains membership in the actual C1-only family, a base-valued
fixed C1 word, public transfer/append context, and all `CopyConditions`:
local residuals, total/inactive helper boundaries and all four active-row
slot non-poles, including empty/zero-weight slots. The member/helper may be
selected later from that earlier family; no late C2 table is frozen before
lambda. The same already-defined collision set is reused, with no new
probability union or second charge.

`AmountFacts` is the preceding proved endpoint's conclusion, not a valid
output-note or validator-success premise. A caller composes the two stages
by retaining the earlier collision branch and invoking this theorem on its
amount-success branch. Both branches use the same member and collision set.

The upstream **own-supported component tuple** gap remains: a high-support
gamma batch alone does not establish C1-family membership. Acceptance
enforcing these semantic/copy premises is also not proved here. This leaf
does not claim occupied output-pair validity, input owner/path/nullifier
validity, append transition, caller authority, spent-nullifier freshness,
full Rust/compiler interpretation or a checked complete payment witness.
The raw table is a mathematical canonical view; allocation of the exact
1024-by-16 Rust vectors and authenticated extractor access are separate.

## Source provenance

Draft parent: `e969d9fa5378dd1e548c8b64b79a9e76a2270d66`.
Checked working parent: `96046bac27e443a67cd4a3820d1c0801f94816fa`.
The inherited runner's original overlay parent remains
`289d7356c78a4cd493fe61a54f9548f2a0c11298`, not the working parent.
V7 gate/sponge reuse is inherited through the already-green
`SelectedOutputNotes`/`SelectedNoteRecovery` chain pinned to
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; it is not replayed here.

| Source-review input | SHA-256 |
| --- | --- |
| New `SelectedEarlyC1Outputs.lean` | `6da1be45f88967fa924d2fbd523193b6791610407b0c4b2149c6ce0b724f36ae` |
| `SelectedEarlyC1Amounts.lean` | `146ad131832ffe3a16ee34f6b3ff5491627d52bb9a22c547bfb3cc3920a05318` |
| `SelectedOutputNotes.lean` | `e7a51e542c33f0c90db5330d43ad02d3dbe405e4c89cd1f01f02e30963e9b2bb` |
| `SelectedCopyAliasQM31.lean` | `a82ddcae4dffa1c8c5e9c3e6a0b65a9a385f1cce425b5eb2d17dde362594e3cb` |
| `SelectedCopyLayout.lean` | `6cd33c59ff9507c48682319d31dff95c91a1862f434f21fb9e63b177acade362` |

## Focused verification and retained failures

| Attempt | Exit | Wall | Peak RSS (KiB) | Swaps | Result |
| --- | --- | --- | --- | --- | --- |
| `selected-early-c1-outputs-nuc-v1` | 1 | 0.96 s | 2,106,668 | 0 | Import failed: missing `V7PairLeafOccupancy.olean`; no theorem audits |
| `selected-early-c1-outputs-nuc-v2` | 0 | 3.67 s | 6,715,072 | 0 | All nine audits standard-only; registered provenance unchanged |

Both attempts retain their exact `-source.txt`, `.log` and `-manifest.json`
files in `experiments/`. No failed source was discarded. Source SHA-256 is
unchanged from the table above. Green output SHA-256:
`29caa06c61159b1b1507f987811abe68ae9cca807e2a38cddbffe31bd1025ad5`.
The v2 per-run manifest is
`6e8679525424116bceae810d345bc346bbe37eee7e1acd18b5fe6586fabafce9`.

Only this leaf was compiled, using Lean 4.32.0 / commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`, `-j1 -M9500`, the inherited
`run_higher_y_nuc.sh`, and Tailscale endpoint `100.108.41.90`.
`HostKeyAlias=nuc.local` only selects the verified key; it is not the network
endpoint. Recorded cgroup limits: high 8 GiB, max 10 GiB, swap max 0,
CPU 200%. The host had no concurrent compiler scope and 43 GiB available
immediately before launch. No laptop compiler, cold dependency build,
resource increase, production edit or broad replay occurred.

## Copy-only cache repair

`append_early_c1_output_cache.py` validated borrowed source bytes against
the exact V7 pin, retained green logs/trace outputs, matching Lean headers,
and existing import-boundary hashes. It copied seven absent source/output
pairs: `Pool.V7PairLeafOccupancy`, `V7PairForestGatedMerkle`,
`HashMerkleModel`, `V5AcceptedSpendRelation`, `V5SelectedGoodVerifierRelation`,
`V5SelectionHidingAbort`, and `SoundnessWorkNormalizedEndpoint`.
It also copied missing `ArithmetizationCore` and `ValueConservation` sources,
checking but not replacing their existing compiled artifacts. This was 16
new files and 18 manifest registrations; no existing source/output bytes
or prior green state were changed.

The occupancy output `a483f5baa7101d3c3a3ca6ceb86b7f40993f3fa4f68bfb20d372c05aa5437e6a`
is the retained `selected-pair-cache-v1.log` green result (9.66 s,
5,627,969,536-byte RSS, zero swaps), with source
`eaf609988c11ce5feceac03a7771a143eaccbad8f1025cee0cf0be89c3b350c1`.
The gated-forest output
`f832d8a65a4eae27cceb5843a46942f017dd76495e562413f51e7be9f1b138b2`
is the retained `selected-forest-cache-v2.log` green result (6.22 s,
5,625,856,000-byte RSS, zero swaps). The remaining local compiled outputs
retain their successful Lean 4.32 trace files and matching hashes in the
cache receipt. These are reused artifacts, not new compilation credit.
The transitive V5 soundness modules supply declarations only: this leaf
does not borrow their old work/grinding probabilities or inventory sizes.

The base manifest changed from
`001f1020072a53448a455d85eeb1568a1c8cb09125bc025b5d4188d230882fec`
to `09afd20a950d3d79d5d9c0df8e7147551c1f288e271f6b0bebcaaa2ec9a91d31`
(800 to 818 entries). V2 checks 943 registered per-run entries before and
after compilation. This registration check is **not** a claim that the
older manifest already covered every existing transitive research import;
notably `SelectedOutputNotes` was already present but unregistered. The
coordinator was notified for the separate full import-closure receipt.
Native package caches remain pinned-revision boundaries, not recompilations.

`early-c1-output-cache-evidence.json` records the append plan/receipt and
their hashes; `selected-early-c1-outputs-evidence.json` records both focused
attempts. The unchanged original append snapshots, copied cache artifacts
and local traces are retained under `experiments/.early-c1-output-cache-evidence/`.
That ignored 15 MiB cache and the ignored green `.olean` are not publication
requirements. The clone-portable `audit_early_c1_outputs.py --check-recorded`
always validates the tracked source, both attempt triplets, both old green
dependency logs and the exact published JSON receipt. It reconstructs the
800-entry before and 818-entry after base manifests from the tracked per-run
manifests and verifies their original hashes and exact appended entries.
It verifies each ignored local output/cache copy only when present; a
present but mismatched copy fails. Missing local artifacts do not erase the
recorded hashes or amount to a fresh kernel replay. Native trace/green-state
hashes remain receipt facts when their optional local bytes are absent.
Ownership is limited to the new output leaf, this review and its focused
cache/check evidence. No unrelated untracked work, commits or pushes.
