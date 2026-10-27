# Frozen2 schedule normal form

`RowOrder_FrozenSchedule.checkpoint_eval`, `after_batch0`, and `decision`
prove the complete frozen2 model decision's ordered log and verdict in the
parsed/input/opening class. The normal form retains batch0, then the six
checkpoint reads (proof/public/body, repeated in that order), then batch1.
Finish consumes the actual completeState. The decision theorem needs no
acceptance premise: batch0 rejection keeps exactly its prefix; batch1 rejection
keeps batch0, the six reads and batch1's prefix. No probability law, query
budget or rejection effect is silently changed.

Attempt005 exit0,1.883621577s,peak4323456KiB,swap0,revision5650ee5670 dirty
with exact source hash in receipt. Every new theorem uses exactly the standard
axioms [propext,Classical.choice,Quot.sound]. Two unused-simp warnings are
retained; no failed proof or resource issue. The existing pinned model objects
were reused in the coherent workspace, under6G/8G/swap0/tasks64 and -M7000.

This is a model normal form, NOT the desired rust-to-model identity. It supplies
an explicit ordered target for the source-row assembly. No source row is
discharged by this stage; its guard/parser/query/input/opening hypotheses are
model conditions, not assumptions that an accepted Rust execution satisfies
them. Establish those from the actual source dictionary before using this as
an accepted-verifier join.
