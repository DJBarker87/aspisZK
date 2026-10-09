# NONE-branch support cap

New source: [SelectedHigherYNoEarlySupport.lean](experiments/SelectedHigherYNoEarlySupport.lean).
Status: **GREEN, focused NUC v2**. All three declarations use only
`propext`, `Classical.choice`, and `Quot.sound`. The changed-source check
finished with exit 0 in 2.95 seconds, peak RSS 6,868,092 KiB and zero swaps.
No probability bound is claimed. Only this leaf was compiled; its source,
green output and both attempt triplets are frozen. The source header's
historical draft label was preserved with the exact checked source bytes.

## Exact endpoint

`no_early_support_cover e checked Gamma absent` uses the literal mathematical
option `earlyC1 e.c1 = none` and returns both:

    (NearGammaSelectedC1.good e.c1 e.c2 Gamma).card <= 63

and, for every gamma in the original Gamma and every actual quotient Q,

    image_valid((atGamma e.data gamma), Q)
    and gamma not in NearGammaSelectedC1.good e.c1 e.c2 Gamma
    imply fibreCount (e.raw gamma) Q <= 252847.

The image predicate is written out as the two selected equations on Q's
cells 1023, 1022 and 1021, with the actual `atGamma` coefficients. The same
Q supplies both image validity and full-fibre support. Neither literal-family
membership, a retained factor, regularity, nor a particular final is needed:
the pointwise implication covers a larger deterministic class.

The Good set depends only on the fixed C1/C2 words and Gamma, not OOD answers,
Q, or any later history. Q is quantified after gamma, so this endpoint also
applies when a later strategy chooses it. It is not an efficient selection
algorithm, an authentication theorem, or a claim that an early option of
`none` means no payment witness exists.

## Source-shaped proof chain

| New declaration | Existing proof consumed | Exact consequence |
| --- | --- | --- |
| `large_support_mem_good` | `SelectedRegularLowSupport.full_bad_card` | At least 252848 full quotient fibres implies at most `262144-252848 = 9296 = 4*2324` bad quotient fibres. |
| same | `SelectedComponentGame.good_of_close_image` | The image-valid actual Q puts gamma into the original-code Good set at radius 9301; reconstruction retains its existing deterministic pole loss. |
| `outside_good_support_cap` | `large_support_mem_good` | Contraposition yields the cap 252847 for every image-valid Q outside Good. This implication itself does not require early-C1 absence. |
| `no_early_support_cover` | `NearGammaSelectedC1.no_early_c1_forces_sparse` and the cap | Absence rules out that theorem's dense branch, giving Good cardinality below 64, together with the uniform complement cap. |

These are named symbolic applications plus small natural-number arithmetic.
No enumeration of the field, code, whole-fibre domain, or recurrence is used.
The pole set is not removed from the virtual word, and Gamma is not filtered
and renormalized. Gamma membership is necessary for the Good-set inclusion;
Gamma nonemptiness and gamma being nonzero are not premises of this leaf.

This is the older **29-lane original-code Good** set at radius 9301, not the
three-helper `ThreeHelperClaimCover.goodGammas` set at radius 61338 on the
own support of a supplied early C1 message. No early message is fabricated
to apply the latter conditional theorem.

## Remaining boundary

The NONE branch still permits the support band **200808 through 252847**
outside these 63 gammas. The existing LOW layer cake is capped at 200807 and
cannot consume this larger interval unchanged. A separate support-tail and
moment integration is required. The retained higher-factor root condition,
common-row singular exceptions, actual compact-suffix score, and source
challenge law remain separate; no probability or acceptance implication is
asserted here. No scalar repair term has been counted.

## Source and cache provenance

Working source parent: `354fbc6e298054057a8303e7e79c9a2560ffc0a5`.
The inherited NUC overlay records research parent
`289d7356c78a4cd493fe61a54f9548f2a0c11298` and borrowed V7 source pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; those are cache provenance,
not a claim that this new leaf exists in either older revision.

Green source SHA-256:
`f460892d61f8c65ddf4ba78f34aab4f05ca142088ef2e7b650662e424d7e759a`.

Both direct imports and the underlying sparse theorem are already recorded
as source/output pairs in the local retained manifest
`experiments/selected-regular-low-probability-nuc-v3-manifest.json`:

| Module | Source SHA-256 | Cached olean SHA-256 |
| --- | --- | --- |
| `SelectedRegularLowSupport` | `4fdefe2e4a7f6f44e66461871b3c8dbcc4b8377abd0bd50729fc154202faf70b` | `178528b724f6e34c559a672e7dedb67544300139fc6958a7ddd89ce316802ce2` |
| `SelectedComponentGame` | `0d1973474b57b8c5c6c03283c2012c8ec28a562fb00b3b51dd17690bad34645f` | `abfdf2165ef398f16f804b4eccc633a44a76cdd9a3f103f08c6fc8b58a28555e` |
| `NearGammaSelectedC1` | `625bd68d1d317ba0738144c6428ebc2773e8ad351791910916349af98d7c2779` | `d4c9935d545bd2c0ec80bd9c2542f0a53d3f2fc88b2e267abfaa5e3a64000857` |

Local source hashes match that manifest. No new dependency export or replay
was needed. The subsequent authorized run's own manifest checked 973 pinned
entries before and after the successful v2 check, with
`PROVENANCE_UNCHANGED=true`. Native package artifacts remain a pinned-revision
cache boundary, not a new package-compilation replay.

## Focused verification and preserved failure

| Attempt | Exit | Wall time | Peak RSS (KiB) | Swaps | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| v1 | 1 | 3.61 s | 6,831,640 | 0 | Missing `GammaComponentGame` namespace for `atGamma` |
| v2 | 0 | 2.95 s | 6,868,092 | 0 | All three standard-only audits |

V1's only declaration errors were unresolved `atGamma` names in the image
predicates. All three dependent v1 audits contained `sorryAx` and are
rejected. V2 added only `open AspisV8.GammaComponentGame`; it changed no
theorem statement, predicate, source mapping, arithmetic bound or resource
limit. The exact one-line difference was checked before rerunning.

Both checks ran serially after explicit root grants, using Tailscale's
numeric address `100.108.41.90`. The remote task was
`/home/dombarker/project-offloads/aspis-higher-y.fMoMeX`; the launcher was
`bash TASK/run_higher_y_nuc.sh TASK SelectedHigherYNoEarlySupport TAG`.
Tags were `selected-higher-y-no-early-support-nuc-v1` and `-v2`.
The runner logged the actual command `lean -j1 -M9500 -R OVERLAY -o OUTPUT
SOURCE` using Lean 4.32.0, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`.

The cgroup recorded MemoryHigh 8,589,934,592 bytes, MemoryMax 10,737,418,240
bytes, MemorySwapMax 0 and CPU quota 200%. Read-only preflights found no
running compiler scope and approximately 49.92/49.97 GB available memory.
Existing host swap usage was not assigned to these jobs; each job reported
zero swaps and prohibited swapping in its own cgroup. The sole compiler
slot was released immediately after v2 terminal completion; no subsequent
build or source edit was performed.

The three green audits are `large_support_mem_good`,
`outside_good_support_cap`, and `no_early_support_cover`. Both attempt logs,
per-run manifests and exact source snapshots are retained locally under
`experiments/TAG` with suffixes `.log`, `-manifest.json` and `-source.txt`.
The ignored green `.olean` was copied and hash-checked; publication does not
require committing that platform-specific artifact.

Exact SHA-256 evidence:

- V2 source and snapshot:
  `f460892d61f8c65ddf4ba78f34aab4f05ca142088ef2e7b650662e424d7e759a`.
- V2 olean:
  `2fe1e0af1b80067a0970ceeed796760e536ef41ab4869a6c3fc767d0206252d1`.
- V2 log:
  `e49c7ceab97ebddedb17b3ddd50a77d1e9a7efea197a5e0a8b3ed4de4bf0e257`.
- V2 manifest:
  `dfa186eeb752e3f4e2671cc3cf5efa99f695a168971764f52f040531d40a4432`.
- V1 source snapshot:
  `c46e1bd6966d79123e423af01b624fa390287237b1daac2c51a7bbf723141165`.
- V1 log:
  `c879b267ee3681195e116f58e33ce59ad20346fe49256fceea172203e720655a`.
- V1 manifest:
  `5a136394268c00da85bbf7768e3bbf37fb3f233803521f4b1f879aab46950f52`.
- Frozen runner:
  `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.
