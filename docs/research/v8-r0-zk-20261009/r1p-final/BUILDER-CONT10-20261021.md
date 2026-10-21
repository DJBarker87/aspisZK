# Builder continuation 10

Branch `codex/cx-builder-ref10-20261021`, base `e5d6d81a5`.

## Stage 1: destructor field composition

`BuilderDropFields` composes the existing projected volatile-word contract
at byte granularity. `word_bytes` and `column_bytes` identify exact half-open
byte intervals; `word_frame`, `column_frame`, `frame_compose`, `fields_frame`
and `fields_observation` cover arbitrary word counts, initial bytes and lists
of fields (in particular the sixteen Vec columns). No disjointness between
columns is needed for the frame result; retained output must be disjoint from
the union of buffers. J9378: exit 0, 1.39 s, peak 2,537,168 KiB, zero swaps;
nine allowed-axiom audits. J9377 was an elaboration failure corrected by
closing a definitional equality; no resource failure or cap increase.

No whole-frame Kani check or unchanged store check was rerun. The existing
57-check projected store certificate is inherited. The new theorem composes
its write-set shape for arbitrary lengths. Actual pointer-to-byte enumeration,
iterator traversal and allocation/deallocation semantics remain source
correspondence obligations; the model theorem alone is not that certificate.

## Stage 2: forest standard library and validator

Pending.

## Stage 3: shipped runtime inhabitant

Pending.

## Stage 4: checker/retry coupling and Source5

Pending.
