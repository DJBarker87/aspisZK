The four existing `r18-sparse-source-world*-{relation,joint}.log` files are condensed summaries only.
The exact captured NUC service output is in the corresponding `*-raw.log` files,
retrieved verbatim from `journalctl --user -o cat`; these include launch commands,
RUSTFLAGS, compile output, test stdout, `/usr/bin/time -v`, and service results.

Units: `aspis-r18-world0-rel`, `aspis-r18-world0-joint`,
`aspis-r18-world1-rel`, `aspis-r18-world1-joint`.
Caps were set on each unit as MemoryHigh=5G, MemoryMax=7G,
MemorySwapMax=0, TasksMax=128, with cargo `--release --jobs 2`.
