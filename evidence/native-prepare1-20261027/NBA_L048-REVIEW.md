# Materialization memory review

L048 failed at Lean's fixed -M7000 kernel memory ceiling after101.676233130 s,
peak7168644 KiB, swap0. The repeated simplifier built a large proof for the
16-call source body despite symbolic replies. It is not credited: its diagnostic
axiom print even names the rejected declaration itself. At a read-only check
95 s into the run, compiler RSS was7136308 KiB. A TERM request was issued after
review, but the process had already exited (kill: no such process).

Replacement: remove repeat/simplify over the whole source. Emit one explicit
rewrite for each digest return, store and readback, applying the existing tiny
eight-slot symbolic lemmas. No cap/time/recursion/heartbeat increase. If the
explicit sequence still builds a large proof, isolate each digest-pair segment
as its own lemma before any further attempt. Never import a failed object.
