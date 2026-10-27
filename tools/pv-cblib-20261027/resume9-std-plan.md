# Remaining std/alloc routes

- op26: extract borrowed resize/append reference, then prove byte contents and
  checked UTF-8 adapter. New P6 native link covers byte lengths 0–2 and every
  output coordinate. Preserve the exact bounded/native-toolchain limitation.
- op33: extract Copy-only borrowed resize reference, prove shrinking avoids
  the clone branch, and prove exact last/take contents. Actual payload is
  Result<Word,Error>; both are Copy in frozen Rust. A small u8 link is a new
  control-flow gate on this changed reference, not a retry of the old u32 or
  Word arithmetic/copy gate. No unbounded/deployed payload association is
  inferred from that bounded run.
- op36: extract borrowed Slice result reference returning an owned error
  image using `to_vec`, avoiding Vec clone's escaped-reference frontier.
  Bind the complete generic guard/copy kernel, preserve Err contents, and
  keep the full N=1024 native success/owned association explicit. No old
  timed-out or rejected array gate is rerun.
- op32: keep NATIVE-EFFECTS.md unchanged.
