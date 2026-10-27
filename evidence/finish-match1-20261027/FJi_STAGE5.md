# Tail and base packing

Checked tail53: `FJi_TailTrace.value` interprets the SAME g[28],g[26],g[27]
and actual three byte reads in installed order. The EbyK new/push/finish values
are composed, with decoder canonicality derived on their own successful reads.
Canonical g is an explicit local condition at this helper boundary; it is not
counted as discharged at the deployed top. No extra owner row was installed.

Checked packing55–58: `FJi_WidePack.scalar` distributes the base scalar across
all eight tower coordinates; `FJi_HeadValue.value` packs the canonical26-term
coordinate sums; `FJi_PackCoefficient.value` reconstructs the SAME selected g[n];
`FJi_PackProduct.value` identifies each actual scalar product in the tower.
The dot-sum recurrence and complete four-slot composition are next.

Decoder receipts45,47–50. Failed46 (Option residual massert),51–52 (small checked
index/coordinate rewrite),54 (tower-zero pattern),59 (reserved name) are retained;
none is accepted proof evidence. No memory kill, timeout, cap increase, source
protocol/dictionary adoption or ELF change. Successful axioms standard-only.
Exact per-target revision, source/dependency hashes, command, exit, wall, RSS,
swap, cgroup and axioms are retained in each receipt directory.

No actual deployed premise has been removed. Rc10 and FIr ledgers are separate,
unchanged; FJi_recount.py checks each immutable ledger and emits zero deltas.
