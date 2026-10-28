# Resumed admission refusals

36021: upload admission refused 2026-10-28 10:53:00.637803 UTC, exit 78,
allowed=false. Retried same ID at/after 10:56:25 UTC (over 180 s), passed.

36049: scope admission refused 2026-10-28 11:26:25.644103 UTC, exit 78,
allowed=false. Original admission and logs retained under refusal-36049-*.
Retried same ID after 11:29:33 UTC (over 180 s), passed.

36052: scope admission refused 2026-10-28 11:32:46.926205 UTC, exit 78,
allowed=false. No compiler started and neither 36052 nor subsequent queued
36053 was consumed. Same-ID retry must be after 11:35:46.926205 UTC.

These are resource contention, not proof errors, admissions or charged
compiler attempts. No scope was started while refused; no barrier was edited.

36052 retry 2: the pre-scope reservation passed, but the in-scope barrier
refused at 11:37:09.099374 UTC, exit 78 / allowed=false. No compiler began.
The second refusal is retained under refusal-36052-2-*. Same-ID retry is
permitted only after 11:40:09.099374 UTC.

The optional fxmem2 citation was not used. At 11:35 UTC the previously named
fxmem branch ref was no longer available locally; the original witness's
committed SHA pins remain retained, and no new reached-destructor proof is
asserted from an unavailable/in-progress source.

36052 retry 3 passed (1.31 s Lean). 36053 upload admission then refused at
11:41:31.514564 UTC. Same-ID retry after 11:44:47 UTC passed, followed by
36054 and 36055. 36056 scope admission refused at 11:47:21.293233 UTC; no
compiler started. Retry is permitted after 11:50:21.293233 UTC.

36060 admission refused 12:08:46.196229 UTC; retried after 12:12:35 UTC and
compiled successfully with the repaired public-import closure.
36066 in-scope barrier refused 12:25:35.442703 UTC (aggregate reservation),
no compiler started. Same-ID retry is permitted after 12:28:35.442703 UTC.

D372: 50434 barrier refusal at 13:39:32 UTC; retried with the same ID.
The retry was 57.47 seconds early; D372-COOLDOWN-DEVIATION.json records this
and the wrapper correction. 50452 upload refusal at 13:47:45 UTC consumes
neither a compiler attempt nor its ID; its full 180-second cooldown is
now enforced by the wrapper over both upload and barrier refusal records.

Final D372 refusal accounting is d372-refusals.json: six uncharged refusals,
IDs 50434/50452/50453/50468/50478/50482, all reused for their eventual compiler
starts. The first retry's deviation is explicitly recorded; the remaining
five retry admissions were 181.8–182.5 seconds after their refusals.
