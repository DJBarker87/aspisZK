# V374 plan v2.2 amendment — LOG D299

Preparation only; target not yet established. This amends [v2, including its
v2.1 thermal amendment](V374-PLAN-v2.md). V2's twelve experiment definitions,
classes, kernels, 1,000,000 calls/class, 10,000 balanced untimed warmups per
experiment, CPU assignment, crops, both Welch orders, threshold |t| > 4.5,
and abort conditions remain unchanged. V2.1's CPU-only monitoring supersedes
the original thermal rule. No qualifying samples are authorized by this file.

## Reason and preparation amendment

D297's [D295 diagnostic evidence](../dudect/DIAGNOSIS.md) supports a harness/setup
artifact: with common fresh-buffer preparation the fixed/random maxima fell
below 4.5, as did fixed-A/fixed-B and random/random controls. This does not
identify buffer identity as the sole causal mechanism or qualify D294's data.

The harness now pregenerates an input record for every shuffled schedule entry,
including warmups. Both classes draw seed, scalar, QM31 and sixteen limbs by
the same generator path; fixed populations replace those values before the
sampling loop. Each call then copies through common fresh stack buffers and
constructs its actual expander and any pole allocation at the same sites.
The pole allocation geometry remains unchanged. There is no retained fixed
seed buffer. Generation, replacement, copying, initialization, allocation and
drops remain outside counter intervals. All twelve experiments and both classes
use this default; no opt-in switch restores the old preparation. Public RNG
seed, population definitions and kernel intervals remain v2's. Pregeneration
changes RNG consumption/order, not the prescribed synthetic populations.

## Built-in campaign sanity controls

Run these first, in order, before the twelve v2 experiments:

1. mask-m31-fixed-fixed: seed A `[0x35;32]` / seed B `[0xa7;32]`.
2. mask-m31-random-random: independent successive random seed records.
3. mask-qm31-fixed-fixed: seed A / seed B.
4. mask-qm31-random-random: independent successive random seed records.

Each control has 1,000,000 calls/class, 10,000 balanced untimed warmup calls,
identical fresh preparation for both classes, and the corresponding original
sampler kernel (counter 0, word 8, actual HOST_HASH). Controls use the same
balanced shuffled schedule policy, CSV format, calibration/crops, two orders,
4.5 investigation threshold and abort rules. They are four sequential sanity
experiments at campaign start, not the six-pair simultaneous D297 diagnostic.
Keep every control result. A crossing is investigated by the lead under the
existing rule; it cannot be ignored to qualify the remaining data. Analysis
runs once after the campaign, with no early clean-pass rule or resampling.

## Thermal qualification and one later window

Retain v2.1: read ONLY x86_pkg_temp and coretemp package/core inputs, list
excluded sensors (including unreadable iwlwifi), wait for package <80 °C
before first sampling (10-second polls, maximum five minutes), and abort if
package >95 °C during sampling. Record temperature and CPU 2 scaling_cur_freq
at every experiment's start/end, now including controls. Unreadable CPU sensors
remain failures. All competing-job, identity, CPU-policy, memory, migration,
marker, sampler-error and deadline aborts remain unchanged.

Stream A's data show package throttling about a third of the time. The lead
should schedule when **both streams are lighter**, allowing drain and cooling
before sampling. No thermostat, firmware, governor or DOITM change is proposed.
The previously dry-tested v2.1 monitor/wrapper under `../dudect/d294/` is the
monitoring authority; do not invoke the original pre-v2.1 window_worker.py.

Request ONE **25-minute (1500-second)** later window, retaining v2.1's envelope:
up to five minutes drain, up to five minutes cool-down, ten minutes sampling
and flushing, and five minutes admission/receipts/slack. Four added controls
add ≤20 seconds to v2's ≤105-second sampling estimate, within the unchanged
600-second sampling deadline (also 60 seconds before marker expiry). Do not
extend the marker or run a second attempt in that window. Stream A's minimum
30-minute separation from another window remains binding. Only the lead may
schedule/authorize that window and operate its marker. D299 requests, creates,
uses and removes no window or marker.

## Artifact readiness and retained limits

D299 rebuilds the tools-only harness and the current recommended devnet_spend
recipe against source b3d109c8ffa47e452b57c5e4a7fe71cfb98e7146 outside any window.
It reruns the conservative instruction comparison and a 1,000/class dry run
labelled **not a measurement**, including all four controls and all twelve
experiments. Exact hashes, resource receipts and comparison limits are recorded
in [the D299 report](../dudect/D299.md) and `../dudect/d299/`.
The later launcher must verify these new executable hashes and use v2.1's
monitor with start/end observations for all sixteen experiments; old ready.json hashes are
historical and must not authorize the new binary.

The recommended build remains pending owner adoption. Source equality and
matched standalone leaves do not establish full interval/whole-route instruction
equivalence. DOITM remains OFF; V371 and V374 remain retained/open. No privacy
premise or T field is removed, added or weakened. No shipped source changes.
