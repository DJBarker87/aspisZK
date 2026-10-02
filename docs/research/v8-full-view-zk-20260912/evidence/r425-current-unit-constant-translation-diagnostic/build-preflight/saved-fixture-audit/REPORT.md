# R425 saved fixture build and execution audit

PASS — Saved R425 fixture build/execution evidence only; no rerun. Fixture success is finite native-check evidence on the exact saved R419 LLBC, not a translator/source correspondence theorem.

The fixture executable target built with exit 0 in 1:22.57, peak RSS 590016 KiB, and zero swaps. The reviewed execution then reported 11 assertions passed exactly once, exit 0 in 0.08 s, peak RSS 38896 KiB, and zero swaps. Both phases have capped systemd and Docker receipts. The earlier v1 execution preflight aborted before execution because the build sidecar receipt was missing; it is retained as a preflight failure, not a fixture failure. The reviewed v2 runner used the saved build hash and checked it against the remote executable before invoking the fixture. Axiom reporting is not applicable. These checks do not establish Aeneas translation or Lean/source execution correspondence.
