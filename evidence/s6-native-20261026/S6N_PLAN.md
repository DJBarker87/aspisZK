# L176 native transport

Baseline e97cb3923c111d0c3f49968bd76ba05417d158c7; Rc7_Top.deployed.
Only S6N_ modules and this receipt directory may change. No shipped or session A files are edited.

Stage 1: pin source and classify semantic_public/common, decoder and Box wrappers.
The inspected wrapper, forest decoder and late decoder use only safe Rust Box construction, moves and immutable borrows; no unsafe/uninit/raw-pointer operation appears. D188 safe std ruling applies to these operations; it does not prove caller installation or effects.

Stage 2: full Result/carrier/error transport and safe getter correspondence in small new Lean modules using coherent SInt2 objects. Reuse prior source extraction only after checking pins.

Stage 3: same-run top integration, before/after statement, ledger recount, non-vacuity and final axioms audit. L176 remains open until deployment correspondence is actually established. Baseline deduplicated 89T/31P/13G; actual 83T/26P/13G.

Host scopes: MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64; Lean -M7000; one scope at a time. Use existing reservation/runner, wait at contention. No package replay.
