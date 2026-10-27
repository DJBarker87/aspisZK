# SCB stage 1: literal replay discrepancy checked

SCB_Replay.annotated_eval proves the complete chronological equation:

    v = eval H (originalWith rust P)
    eval H (annotatedWith D rust P)
      = (v.log ++ eval(H, rust(v.input)).log, (enrich(build(view v),v.input),v.accept))

The only condition is the existing physical-input property: rust depends on
public bytes and stored bytes. SCB_Replay.not_single_run proves that if the
verifier suffix is nonempty, the physical original view is unequal to this
annotated view. No model join, collision exclusion or new runtime law enters.
The same result applies with P replaced by canon(lift P).

Validation: SCB_003 exit 0, wall 1.874141285 s, peak RSS 4,289,900 KiB,
swap 0, source revision e7257391dd plus exact dirty source SHA in the receipt.
All four axioms reports contain only propext, Classical.choice, Quot.sound.
SCB_001/002 are excluded development failures from mistaken library lemma
names; the final proof uses list cases. Neither timed out or was memory-killed.
Every attempt used one module in the unchanged SInt2 workspace/launchers,
-j1 -M7000 -DElab.async=false, systemd 6G/8G/swap0/tasks64. Admission allowed
all launches; reservations were at most 16 GiB before this job's 8 GiB request.

Ledger credit: none. This is a structural obstruction, not SCB_Top.deployed,
and does not yet construct an accepted installed source fixture. The next
focused module will instantiate the exact L159 definition on a faithfully
recorded single execution and give a successful one-query model witness.
