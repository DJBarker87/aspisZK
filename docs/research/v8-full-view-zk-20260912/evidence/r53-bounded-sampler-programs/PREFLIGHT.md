# R53 resource and evidence preflight

Base: `a26a468746e9551769ce1d17104050e1fc1bf1fc`.
NUC reached through Tailscale at `100.108.41.90`. Preflight: 62 GiB RAM,
47 GiB available; only the user init scope running. Historical system swap
usage was 7.5 GiB; every new job below prohibited swap and reported zero swaps.

Jobs ran serially in separate user systemd scopes with TasksMax=128:

- Focused Lean leaves and fixture export: MemoryHigh=3G, MemoryMax=5G,
  MemorySwapMax=0. Source-aware cached workspace advanced through a–j;
  final workspace `aspis-r53-lean-20260929-j` contains 279 successful objects.
- Rust source replay: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0.
  Expected expensive phase was release compilation, not elimination or proof
  generation. Cargo used --release --locked --offline --jobs 2 and retained
  overflow checks. Maximum simultaneous reserved memory was 7 GiB.

Focused failures are retained: c (scan branch simplification), e (nested
sampler branch split), h (explicit list nonmembership/length facts), and i
(the exporter used reserved keyword `export`). Each was repaired before
rerun; no limit was increased and no unchanged full suite was rerun.
No large finite-support enumeration, recurrence normalization, cold Lean
dependency build, Aeneas replay or SBF rebuild was attempted.

Lean fixture generation evaluated the executable oracle programs directly,
not their finite all-branches support. Original fixture bytes remain on the
NUC; the archive contains a gzip copy checked by decompressed SHA-256.
The source runner checked the retained 197-file control manifest and added
only the test target and its Cargo entry. No production source was edited.
