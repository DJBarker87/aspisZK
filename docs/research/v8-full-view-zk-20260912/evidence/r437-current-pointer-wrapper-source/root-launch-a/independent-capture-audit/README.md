# R437 command and saved-capture audit

This read-only check compares R437's saved launch scope and capture with R434. The command is exactly R434 plus the requested `core::ptr::non_null::NonNull` and `core::marker::PhantomData` includes and a fresh destination. Root, source pins, baseline, compiler/toolchain, release flags, and remaining arguments match the saved receipts.

The captured extraction and GNU time both exited 0. The LLBC has `has_errors=false` and SHA-256 `bafe9c1297a8ea92eaea3c37c685da3f5d3fe2e04c335ac9f1f4d64c4312386c`. GNU time records 15.09s, 630,164 KiB peak RSS, and zero swaps. The terminal cgroup snapshot independently records the effective 5/7 GiB, no-swap, 128-task limits and zero memory events; its peak is kept separate from GNU RSS. Source hashes match R434's terminal snapshot.

This is diagnostic LLBC evidence only. It establishes no formal axioms, pointer-layout theorem, or Rust source-semantics correspondence. Run `python3 audit_capture.py` here for a fresh report; the script does not modify the saved capture.
