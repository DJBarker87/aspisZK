# EJR launcher reconstruction

Base: committed prover-commit50-20261022/harness/run-joint.sh. Environment:
prover-commit54-20261023/build/J.json copied verbatim. run2.py: newest committed
*.py copies identified with git log, compared byte-for-byte with the later
sim-cost5-20261022/run2.py.txt and invocation in Stream B's fragment.

Changes to launcher: restore Stream B's 20000–29999 range and historical
5000–5799/6000–19999 ranges; add 30000–39999 for recovery; explicitly reject
20000–27099 as already used. sent.txt retains recovered source/env/attempt
triples and comments marking allocations. No fake source hashes assigned to
unobserved attempts. 28000–29999 remain Stream B's reserved replay allocation.
Quiet-window block is deliberately omitted per latest explicit instruction;
the existing ~/.local/bin/systemd-run shim handles quiet windows.
Caps are fixed at 6G high / 8G max / swap0 / tasks64 / -M7000. Slot locks use
existing /tmp/aspis-r0-lean-slot-{1..4}.lock or global lock; no external flock.
The historical disabled slot branch is restored to its documented night-window
condition. This worker invokes only one scope at a time.

No theorem or shipped-file change. Exact target: launcher/environment/driver
restoration; no Lean execution in this stage, so exit/wall/RSS/swap/axioms are
not a proof result. File SHA-256s and remote equality checks are in the stage
receipt. Top theorem before/after unchanged; ledger premise delta 0.
