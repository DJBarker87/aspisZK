# Native shape splits

K002: full 1520-byte late-buffer oracle mutation timed out after its fixed 90s solver limit; no credit.
K003: replace it by a single arbitrary byte in that buffer. Establish all-byte initial zero by arbitrary index and prove the caller ignores every returned buffer value in Lean.
No timeout/cap increase. Retain the same harness identifier; the source mutation is pinned in each run.
