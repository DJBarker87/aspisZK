# R497 concrete slice-length builtin tool candidate

This archive preserves the exact translator-source patch, unchanged R491
`PrePasses` source, and capped release build records. The one-line patch keeps
the existing generic slice-length registration and adds the exact selected
`core::slice::{[u8]}::len<u8>` registration to the supplied `Slice.len`
builtin. It does not include the rejected generic `<@T>` alias.

The build exited 0 in 0:04.00 with peak RSS 502,444 KiB and zero swaps. The
candidate binary is retained on the build host at the path recorded in
`build/candidate-binary.sha256`; it has SHA-256
`85a1037c1d2e675907c4a9c3b0b87e671633f9284775b1be8720f8f208b4086b` and
size 49,496,368 bytes. No translation or Lean compilation is claimed by this
tool-build archive.
