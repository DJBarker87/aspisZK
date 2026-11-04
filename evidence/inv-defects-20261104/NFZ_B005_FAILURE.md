# NFZ_B005 own-wrapper failure and mandatory stop

B005 admitted on exit 0 and allowed=true after NFZ_PAYLOAD_PREFLIGHT.json PASS and a byte-identical local dry staging of 484 text + 11 binary files, including all transitive literal includes. Caps: MemoryHigh6G / MemoryMax8G / MemorySwapMax0 / TasksMax64. Stable rustc/cargo 1.94.1; CARGO_BUILD_JOBS=1, cargo -j1, RUSTFLAGS=-C codegen-units=1; one-token jobserver, one-CPU affinity. Measured cgroup thread peak17 over2401 samples at10ms (receipt). No -Z option was used.

The library cargo rustc command finished successfully in15.53s and emitted the retained NFZ_B005_aspis_r1_cost_probe-2af8d844c3814c6b.mir.xz. The program command failed during libc0.2.186's build script. Cargo removes RUSTFLAGS from the build-script environment; libc probes rustc through RUSTC_WRAPPER. NFZ_rustc.py line7 accessed os.environ['RUSTFLAGS'] and raised KeyError. This is my own overly strict wrapper, not a frozen-source failure, timeout, memory kill or host-infrastructure failure.

Exact failure: libc build.rs:219:5 `failed to run rustc`, caused by `KeyError: 'RUSTFLAGS'` in NFZ_rustc.py:7. Program cargo returned101; check=True raised CalledProcessError; NFZ_scope.py returned1. Full log and original exact sources are in NFZ_B005/. Receipt:25.118775121169165s,751856KiB peak child RSS,swap0,1007034368 bytes cgroup memory peak. All495 source pins and lock validated after failure. No second launch occurred.

The binding lead instruction says: “If scope 1 fails for an own-script reason again, STOP, do not use scope 2”. Thus B006 is deliberately UNUSED and the job stops incomplete. Retained partial library MIR is not a complete caller/independent authority or an admitted edge. No new reachability exclusion, row or closure credit is claimed.

Corrected wrapper and command are recorded in NFZ_REMAINING.md, not executed. No remaining scope is usable under the current instruction. No additional compiler, Kani, Lean or extraction attempt is authorized by this packet.
