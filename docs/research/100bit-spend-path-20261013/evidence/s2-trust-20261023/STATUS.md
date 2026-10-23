# S2-T stage 1: production library pins

Production Cargo.lock is byte-identical to the retained S10 adopted-ELF rebuild
workspace lock (SHA-256 5782e6a3...). Both SDK crates are 2.3.0; cached crate
archive hashes match lock checksums. production-pins.json pins complete source
files and inclusive source spans. The production adapter imports the
solana-program re-export of solana-account-info.

The SBF source is the installed platform-tools v1.52 core/cell.rs, not the
v7 Kani nightly source. RefCell uses an isize BorrowCounter. Ref and RefMut
contain BorrowRef/BorrowRefMut; structural Drop invokes those counters' Drop.
Ref has no DerefMut. The installed rustc reports commit-hash unknown; version.md
names the Anza source commit, but compiler/source correspondence remains P6.
This limitation must travel with the trust pin.

Target: source pin collection only. No compilation or proof run, hence wall/RSS/
swap/axioms are not applicable. Source revision and inherited build references
are in production-pins.json and ../s10-repin-20261022/build-default-v2/.
No release artifact changed; default 40dc7574..., devnet 12cb0bc2..., Pool
121f3e29... evidence is reused, not rebuilt or re-certified here.

No assumptions discharged. Route B retains the newly authorized SDK trust
boundary and P6/runtime/library-source correspondence. Next: exact universal
fifteen-field interface, concrete consistency model, Kani spec and audit.
Budget used: Lean 0/100, Kani 0/60. No shipped-file changes.
