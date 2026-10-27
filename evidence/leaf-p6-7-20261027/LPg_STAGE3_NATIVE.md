# Small native contracts and loop stages

K003 canonical reduce range on arbitrary u64 PASS; K004 scalar add on arbitrary canonical u32 operands PASS. K005 Q-add contract failed solely at builtin memcmp unwinding (16-byte equality, unwind6), with293 other checks undetermined. K006 replaces array equality with four scalar comparisons and PASSES without changing caps, timeout or unwind. Original native arithmetic remains unchanged.

K007/K008 echeck one32-byte iteration PASS on arbitrary bytes and arbitrary prior-good Boolean, both k values. K009 compact one16-byte iteration PASS on arbitrary bytes/prior-good Boolean. K010 validator one32-byte iteration PASS on arbitrary bytes/row, exact local error0. K011/K012 expansion one16→32-byte iteration PASS for arbitrary pre-output bytes and arbitrary low/high lane. These local functions execute the original source bodies; no whole-buffer loop is verified.

Still open: association to every reached full-buffer native pre-state; full output-array write/token/borrow/frame installation; same native/model carrier join; use in the actual deployed top. No full leaf CLOSED and no top premise removed. K001/K002 raw products remain unproved; no Dot push caller using raw stub_verified is run.

Frozen graph validation precedes every invocation; post-lock hashes match. Exact patches and receipts retain all variants. New proof helpers are scratch-only. The source in crates/programs in this worktree has not changed, so no ELF rebuild trigger occurs.
