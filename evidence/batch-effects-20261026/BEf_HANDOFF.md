# BEf handoff

**L166 retained; target not yet established.** Branch
`codex/cx-batch-effects-20261026`. No push. The counterexample is to the
existing batch all-Result lowering, not a shipped acceptance vulnerability.
No BEf_Top.deployed is supplied and no premise-removal credit is claimed.

The recovered run had6 Lean attempts,0 Kani. Final totals are **25/100 Lean,
12/30 Kani,3 optimized native Rust runs**. The budgets are NOT exhausted.
The false all-Result item stops under r1p-common rule4, with the requested
counterexample diagnosis preserved rather than an accepted-only replacement.
This does not complete the separate native mutable-carrier association task.

## Counterexample and exact scope

On the pinned adopted transfer-13 compact proof/public bytes, the unchanged
native verifier accepts TX1 and authenticated TX2. R002/R003 then mutate only
unused first-tree padding:

| Reached source batch | Padding offset | Node count | Leaf hashes before Parse |
|---|---:|---:|---:|
| TX1 |32775|138|10|
| TX2 |47015|163|12|

For TX2, TX1 accepts the modified proof and produces the checkpoint actually
resumed by the rejecting TX2. The hash backend is real SHA-256; no source
child, multiproof or hash stub is used. This is native verifier evidence,
not a complete Solana SDK/bank/ELF fixture.

The retained raw Aeneas emission returns `none` at this padding exit; its
enclosing tree converts none to outer `fail panic`. Rust returns inner
`Err(Parse)`. `BEf_Counterexample.rejected_batch_tail` checks inequality of
the LOCAL tail encodings with identical state/history. `BEf_ErrorMaps.current`
and `.stage` show both actual installed error maps preserve the distinction.
Those map facts are axiom-free. The full concrete native fixture is NOT
evaluated end-to-end by Lean. Native fixture, local theorem and source-slice
Kani scopes remain explicit; see BEf_OBSTRUCTION.md and the rejection inventory.

K006/K007 check the complete terminal source slice on a singleton-index
class with arbitrary scratch, frame and zero suffix hashes, with covers.
K009/K012 check the exact source guard at the captured real counts;
K010/K011 check those counts on the actual captured index sets. K008's
combined reached-state attempt timed out and gets no credit. Earlier CPUID,
timeout and memcmp-unwind failures are retained; every retry isolates or
changes the failed job. No cap was raised, no source call was stubbed.

## Before/after, recount and non-vacuity

The actual checked-in top is Rc4_Top.deployed. Before/after statement files
are BYTE IDENTICAL, with retained Conclusion captured separately. The Rc4
atomic-family/shared-dictionary method yields unchanged actual82T+49P,
deployment6T+13P, aliases3P, deduplicated88T+62P. Delta0T/0P/0C; no added law
or trust item. BEf_recount.json pins the baseline and retained L166. P6C's
candidate reductions are not counted again or silently integrated here.

Native accepted-pair/reached-rejection witnesses, Kani covers, local
BEf_Nonvacuity and the inhabited exact D188 source-model witness establish
their stated local non-vacuity. No joint inhabitant of every remaining
runtime/crypto hypothesis is asserted. Generic BEf source-interpreter rules
retain complete failed prefixes and reconstruct chosen carrier transitions;
they do not identify native pending weights, allocator or account slices.

## Validation and next deliverable

BEf_validation.json matches all16 current prefix sources to successful
receipts. Final Audit022: exit0,2.142493s,5250056KiB RSS,swap0,revision
f3e3d87f38 plus exact source/dependency hashes;30 printed theorem audits,
only standard axioms. Counterexample023: exit0,1.814866s,4418428KiB,swap0.
ErrorMaps025: exit0,2.044411s,5255100KiB,swap0. Kani/Rust metrics, sources,
commands, tool pins and scope limits are in numbered receipts. Excluded
timeouts lack aggregate child RSS; their cgroup peaks are retained separately.
All jobs used one admitted6G/8G/Swap0/Tasks64 scope; Lean-M7000; optimized
Rust/Kani. Two quiet-window refusals precede allowed retry03. No package replay.

Next: repair/re-extract the branch-specific pending errors AND scratch, then
prove all-Result/source-effect composition and the concrete native carrier
instance on both slots. A blanket none→Parse decoder change is insufficient.

Only BEf_ modules and this evidence directory changed. No shipped/cfg(kani)
file, other-prefix candidate/worktree, key or funds changed. ELF rebuild
trigger did not fire. Inherited pins, NOT reproduced:
- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548
