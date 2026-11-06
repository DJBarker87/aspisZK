# Failed shapes and replacements (no failed attempt is credit)

Native timeouts: NJF_K001, NJF_K004, NJF_K010, NJF_K011, NJF_K020, NJF_K021, NJF_K024, NJF_K025, NJF_K027, NJF_K029, NJF_K039, NJF_K041. Every run retained the same90s harness limit and6G/8G/swap0/tasks64 caps. No timed-out shape was rerun unchanged or with a larger cap.

- K001 combined full-slice shape: split args/control/scratch/Parts/shared assertions, retaining full oracle mutations; replace unnecessary scratch-oracle copy with per-field writes.
- K004 argument window: initialize every Weights field directly in its allocated Box before Box::from_raw, avoiding whole-factor-array setup copies; every raw field remains arbitrary. K012 passes; copy-specific K038 fails.
- K010/K011 shared window: split partial arguments, high arguments, high pre-state and high partial value. Each keeps full mutable footprint.
- K020/K021 high pre-state: partition slots0..2 and3..6. K028 passes but its control K029 times out; replace that low region by constant observation slots0/1/2 with three matched pairs. K030/031 covers3..6. K032–037 all complete semantically.
- K024/K025 redundant Vec-setup scratch variant and K027 redundant Parts control: excluded. K006/007 and K008/009 are the complete borrowed-slice windows; NJF_ScratchCarrier proves every decoded length64 Vec payload is represented by the array setup. No whole Vec replacement is credited.
- K013/K017/K019 pointer-only failures are historical, not copy-specific control credit. K038 and K040 fail copied ap0 words. K039 common-word inversion and K041 source-word mutation time out; replace the assertion's temporary four-word arrays by their four exact field projections. K042 passes and K043 fails `!same`, with the SAME arbitrary i<16 and limb<8 domain and unchanged parent/oracle bodies.

Lean errors were local source drafts, resolved before admission: L001/L002 error-namespace/type selection; L004–006 let/match simplification; L008 common contradiction/tuple reduction; L010/L011 segment name and projection; L012/L013 nested projection reduction; L017 dependent powers type inference; L019/L023 Classical decidability; L026/L027 global Domain namespace; L029 comparison-token spacing; L038 Subtype projection inference. Error-recovery sorryAx output in failed drafts is excluded; final source hashes match passing receipts and the full raw closure has only standard axioms.

Own catalog validation initially compared optional source_path/source_sha metadata as if part of import identity; repaired to compare the actual imports field, retaining all catalog/source provenance. Every overlapping import list is equal; no import check was relaxed. Own scripts only changed; no lead launcher/reservation/shim/shared workspace changed.

Exactly two complete combined audits ran: L041 historical221-root/15194-module gate; L044 final224-root/15195-module gate after LowSlots was added. L044 retains the full final raw/scan outputs. L041's stdout/receipt retain its actual result; its common-path scan file was superseded by L044, not relabeled as L041. No third full audit or unchanged full regression.
