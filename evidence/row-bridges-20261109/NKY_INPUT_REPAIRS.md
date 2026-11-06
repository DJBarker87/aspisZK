# Owned input repairs

Before submission, the native runner's predecessor-prefix replacement and missing
local input-store directory were corrected. Neither launched a scope.
NKY_K001 exited 1 in validation before Kani: the base source seed lacked KMX files.
NKY_native_seed copied the retained predecessor source read-only into the own
workspace; every imported file hash is retained. The strict validators are
unchanged in meaning. NKY_K002 passed with the same harness name/property.
No timeout or memory-killed shape has been replayed.
