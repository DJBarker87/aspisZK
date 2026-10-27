# Native lower types

Before 26/28. Current 26/28. Type0's descriptor value is already selected;
its world/Drop obligation is separate and remains open.

| Type | Ledger | Status | Required observation |
|---:|---|---|---|
|3 std::io::Error|V268|open|kind, consumed message bytes, retry; resource/effect frame|
|27 core::fmt::Formatter|V269 (+ forbidden route V270)|open|reachable Debug/Display sink calls, bytes, options, failure and sink state|
|File world|V271|open|open/create_new/mode/write/flush/sync/retry/Drop outcomes and state|

No arbitrary dictionary representation or new standard-library axiom is
selected by the proof harness. Error projection tests alone will not be
reported as native type association for every caller and native world.
