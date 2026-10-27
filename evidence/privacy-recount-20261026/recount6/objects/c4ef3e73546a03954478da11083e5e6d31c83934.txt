The sampler differential launch `native-circle-01` was refused by the standing
barrier at 2026-10-27T17:40:08Z: aggregate bounded reservation 59,995,324,416
bytes exceeded the 59,055,800,320-byte safe limit. No test ran. Its complete
admission JSON and log are retained; it is not a compiler failure or a
counterexample. No caps or barriers were changed. No new host scope is
permitted until at least 17:43:08Z; compile-free block-carrier source work
continues during the required wait.

Earlier `aeneas-pop-move-01` was refused when an unrelated cgroup disappeared
mid-scan. Its one retry, after the required 30-second wait, was admitted as
`aeneas-pop-move-02`; the ensuing structured-Drop rejection is a separate,
charged extraction result.

Lean ID 52727 was refused at 17:44:27Z; it is used but uncharged. After the
three-minute wait the private wrapper incorrectly rejected the unchanged
source before allocating 52728 because its hash guard included uncharged
refusals. The wrapper now compares hashes only against charged attempts,
so ruling (d)'s next-unused-ID retry works. No admitted/failed compile can
be retried unchanged, and no cap, shared launcher, or barrier changed.
