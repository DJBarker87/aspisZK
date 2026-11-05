# NIO stage 1: CPI-info carrier windows

K002/K004/K006/K008/K010: the actual frozen exact_transfer_account_infos_v1 returns positions [1,0,3,2,4]. K012/K014/K016/K018/K020: the actual exact_withdrawal_transfer_account_infos_v1 returns [1,0,2,3,4]. Every individual window proves exact key, SAME Rc data and lamport carrier, and exclusion of one arbitrary distinct guarded key held by a real exclusive data guard. The ten corresponding odd controls K003..K021 substitute that guarded carrier and fail semantically. Exact KMX patch and frozen dependency graph checks pass per receipt; no lock drift.

The exact-five validator is a borrowed-place projection stub under the stated length-five, pairwise-distinct key domain. No error variant is suppressed on that domain: the actual validator rejects wrong arity or duplicate keys only. Native verification of its arbitrary-prefix uniqueness loop and the caller's successful domain are still OPEN. These are native local helper windows, NOT complete caller or CPI-site certificates. No instruction-meta list has yet been natively associated with these caller keys. Physical key/cell interpretation and runtime returning frames remain explicit.

K001 is a retained own-input compiler rejection (no_std crate; std::rc unresolved); repaired to alloc::rc and the uniqueness loop was split out of the clone window. It has no native credit. No timeout or memory kill occurred. Full logs contain the actual diagnostics.

NIO_CPI_GUARDS.md identifies each held cell and all four source edges. Callback coverage includes deposit, withdrawal and no-op cases; withdrawal includes marker creation and rechecks, not merely its token invocation. No site is marked discharged or observed-error-arm without its missing native packet. Pool-consumer rows closed: zero.
