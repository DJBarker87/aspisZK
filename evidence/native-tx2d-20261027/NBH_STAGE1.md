# Stage1

L004/L005: exact full frontier loops, all raw-u32 frontiers, including early error. L007: exact afterstate validator Result, every typed afterstate. L014: total byte-array equality on arbitrary arrays, standard axioms only. NBD modules imported unchanged. K002/K003: native one iteration on arbitrary frontier and level<=20 under closed all-raw-limb digest child contract. K004/K005: native ordered prefixes on arbitrary full records. Native iteration/model observation association is next (NBH_NativeFrontier); do not yet claim enclosing validator CLOSED from the separate pieces. No headline premise removed.

K001 was a compile rejection from an incorrectly nested module path; changed super::POOL_V1_PAIR_CAPACITY to crate::pool_v1::POOL_V1_PAIR_CAPACITY. No solver failure or shipped bug. G006 first preflight launched no metadata/Kani: new own sources were not synced; the subsequent sync preserves validation.
