# Native reached rejection cases and split Kani checks

L166 remains open; no deployed premise is removed. The native source evidence
now extends beyond direct synthetic batch calls. BEf_R002 checks an accepted
adopted compact verifier pair, then actual reached padding rejection in TX1
and TX2. For TX2, TX1 succeeds with the modified proof and returns the exact
checkpoint subsequently resumed by TX2. R003 exports its query/index inputs.
Both first-tree padding failures retain10/12 actual leaf hashes and emit no
parent hash after rejection. These are host-native source fixtures with real
SHA-256, not a Solana SDK/runtime/ELF release proof.

Captured inputs/outputs: BEf_reached-inputs.json; exact fixture hashes and
sizes: R002/R003 receipts. Source bodies and local fragments are validated by
BEf_extract.py --check and BEf_native-source.json. No batch, hash or multiproof
source call is stubbed. The source guard's explicit Ok continuation is only
a local fragment boundary and is never substituted into the shipped batch.
The retained raw Aeneas emission already contains the none/panic mismatch;
BEf_rejection-provenance.json pins it before the typed Ops generator.

All12 Kani attempts are charged. K006/K007 passed the complete terminal source
slice for a singleton live index, arbitrary scratch values/suffix, exact
Result, scratch frame, zero suffix digest and reached cover. K008's attempt
on the captured real index set timed out and is EXCLUDED. Its split gates
K010/K011 check unchanged node_count on the exact captured sets (138/163);
K009/K012 check the exact source padding guard at those counts, with reached
covers. These separately checked gates do not claim a new all-input whole
batch refinement. K001 unsupported CPUID, K002/K003/K004 timeouts and K005
memcmp unwinding failure are also excluded. All failures and changed splits
are retained. No cap increase or unchanged timed-out job rerun occurred.

Rust: R001 exit0,44.375862s,592396KiB,swap0; R002 exit0,4.605961s,
195180KiB,swap0; R003 exit0,4.139683s,193088KiB,swap0. K006 exit0,
89.345035s,4711344KiB,swap0; K007 exit0,70.737944s,4089536KiB,swap0.
K009..012 pass in3.7..5.1s with peak<300MiB. Receipts include exact commands,
source/dependency hashes and revision anchors. Timeouts' /usr/bin/time RSS
captures the terminated parent and MUST NOT be read as aggregate child peak;
their cgroup memory.peak (about4.8/6.6/6.6GiB bytes as recorded) is retained.
No memory.max kill occurred. All scopes verify6G high/8G max/Swap0/Tasks64;
Rust/Kani profiles are optimized. One job scope at a time, admission first.

Lean21 passed BEf_D188Witness: an actual source-function model inhabits D188
while its value projections do not determine an extra state projection.
All currently checked prefix modules use only standard axioms. No joint
inhabitant of all deployed runtime/crypto hypotheses is claimed.

The remaining new Lean targets (Counterexample, ErrorMaps, then Audit) are
PREPARED, NOT YET CHECKED at this stage. Admission023 was refused twice by a
quiet window until2026-10-26 18:15UTC. Continue rule6 wait/retry, then compile
023,024,022 sequentially; no gate was bypassed. Budgets at this snapshot:
21/100 charged Lean;12/30 Kani;3 optimized native Rust runs. No package replay,
shipped/cfg(kani) file change, ELF rebuild, other-prefix edit, key operation,
source adoption or new trust item. The standalone evidence harness is new;
its cfg(kani) modules do not modify shipped files. Frozen ELF pins inherited.
