# R440 frozen runner audit

This read-only audit covers the lead-frozen `lead-launch-a` runner files, compares the saved R440 command to the prior R437 extraction command, and checks the completed R440 launch/extraction receipts. It does not edit or execute either runner.

The launch reviewed the exact `crate::freeze` extraction with the same 16 includes, feature set, Aeneas preset, built MIR, monomorphization, default sysroot, offline/locked/release one-job Cargo invocation, manifest, and binary as R437. The only command changes are the candidate Charon wrapper at argument 0 and the fresh R440 output destination at argument 44. The candidate and original driver/wrapper identities and candidate overlays are checked against the saved pins. Source, standard-library, R429/R185/R437 input hashes remain identical before and after capture.

The reviewed systemd unit used `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, and `RuntimeMaxSec=600s`. The reservation record included both system and user managers, deduplicated cgroups, and the active capped `aspis-zk-site.service` reservation. The saved cgroup controls and event counters show zero swap and no high/max/OOM events. The GNU time receipt records exit 0, 13.95 seconds, 630272 KiB peak RSS, and zero swaps. The LLBC was saved with SHA256 `01cd5ddc7086bba5f4e92802f90e59cce4034cf519d495ec35f925b91a6f033d`; `has_errors` is false.

This is runner, custody, resource, and extraction-receipt evidence only. It makes no source-to-model semantic, cryptographic, probability, or release-gate claim. The capture is diagnostic native LLBC; formal axioms are not applicable.

Run `python3 audit_runner.py` from this directory to reproduce the local checks. The checker consumes the frozen runner snapshots, the saved R437 command receipt, and the saved R440 launch/result/reservation receipts. It does not contact the build host.
