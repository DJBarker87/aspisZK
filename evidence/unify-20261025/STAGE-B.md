# Same-witness accepted union

`Uni_Accepted.accepted_pair_unified` passed Uni_003. It obtains exactly one
`f,s,outer,pre,middle,fs,ss,cuts` from Op5T_Final at `Uni_Install.base`.
It derives scan and the TX1 run from those cuts; there is no second call to
an existential accepted-pair theorem, and no new compatibility assumption.

The conclusion is the conjunction of the entire Op5T_Final conclusion
(including Tx2I finish, both batches, both headers, source cuts, expanded and
owned traces, frames, Claims parsing, Required14 continuation) with the
Op4P scan and complete Tx1Q run/WhenBound conclusion. The TX1 helper's
caller digest uses the SAME installed TX2 adapter. The batch conclusion's
let-bound SDK uses the SAME union base, not the former free dictionary.

The free current dictionary is further specialized to shape3/scan4/batch6,
query7/writer16/flush17/pending18/geometry19/initial20. The TX2 stage and
AdapterRw dictionaries remain Op5T/Tx2I's installation, including shape,
batch1 and finish. Exact equality to the Tx1Q specialization is Uni_001;
Uni_002 checks the cuts-to-scan and cuts-to-TX1 bridges.

Before: separate Op4P / Tx2I / Op5T / Tx1Q existential specializations.
After: one existential tuple and one cut proof with their union. All original
SDK/std/runtime/native/extraction/cryptographic and continuation conditions
remain, specialized to this union. Only the old unconditional mark fields
are replaced by Op5T's actual-Rust-Ok guarded fields. No new header, scan,
batch success, query return, writer success, selected cut or accepted native
execution is assumed. `WhenBound` and conditional FinT hypotheses are retained
verbatim, including saved_ten/twelve and Session A laws. They are not discharged
by composing the dictionaries.

L164 is closed for this checked source dictionary/witness chain. This does
not instantiate deployed runtime, oracle log association, model provenance,
writer adoption, or raw canonical frozen2 join. It is not a release theorem.

Uni_001/002/003 exit0; standard axioms only. No dependency rebuild, package
replay, Rust, Kani, shipped source or ELF change. Full fields and source
snapshots are in the per-attempt receipts. Failed/future audit attempts are
not included in this stage's validation credit.
