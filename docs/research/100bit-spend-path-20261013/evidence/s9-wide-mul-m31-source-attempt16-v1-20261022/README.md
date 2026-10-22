# S9 WideExact.mul_m31 attempt16 source packet

This packet retains attempt16 source, tool receipts, translation metadata, normalized Aeneas `Types.lean`/`Funs.lean` inputs, and the three focused R22 source-owner reuse receipts. It deliberately excludes LLBC, Lean objects, executables, and caches.

Attempt16 used a top-level `focused_wide_mul_m31` reachability harness that calls the exact pinned `WideExact::mul_m31` method. The shim only makes the method reachable to extraction; it is not a replacement implementation. The emitted target and its `M31.mul`/reducer descendants were transparent.

This is extraction and compile-owner evidence, not a completed source-to-CurrentWide semantic theorem. The normalized Types/Funs owners are compile-only inputs. The actual operation refinement remains open; its Lean map is an unverified candidate, and the first focused reducer-map attempt failed on wrapper/conditional normalization. The extraction profile does not establish production SBF MIR overflow mode.

The manifest pins all copied files. `check_packet.py` rejects LLBC, Lean objects, Python caches, and binary artifacts.
