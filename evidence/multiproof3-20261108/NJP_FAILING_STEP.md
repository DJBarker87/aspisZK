# Failing steps

K001: compiler setup failure from own empty RUSTFLAGS (multiple input filenames). Replacement K005 uses --cfg NJP_good_argument; same validation, no timeout or memory kill, no semantic credit for K001.

L005: heartbeat timeout in congr tactic while comparing expanded Poseidon terms; no credit. Replacement L006 transports the symbolic seed equality with congrArg and unfolds only nodeCompress/digestOf; cap unchanged.
