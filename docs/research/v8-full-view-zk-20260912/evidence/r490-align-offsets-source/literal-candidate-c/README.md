# R490 literal candidate c failure

This is a failed translation, not a proof. The archived LLBC has SHA-256
`a3295333237b0dfad164b826a6d8ce6b2d183d177ca1453489e0e1d2a74a2698`.
The receipt records exit status 2, wall time 0:00.20, peak RSS 59,840 KiB,
and zero swaps.

The raw log records `Invalid_argument List.combine` while instantiating a
function signature (`llbc/InterpUtils.ml:906-907`). This archive makes no
claim beyond that recorded failure.

`pre-r484-literal-adapter-manifest.json` is the exact pre-change adapter
manifest (SHA-256 `0164ec4db6905e6e4a2ebf8a4a3f3dabd0ef0102bf7ad89f23b88d1b4ee108b9`).
It records the original source snapshot SHA-256
`384d170f403306449c7435e81da6050ae3f447b28a9ab0dc881450c9322621af`, its
reachability and ordered-declaration snapshot hashes, and the previous
adapter's selected global/function metadata.
