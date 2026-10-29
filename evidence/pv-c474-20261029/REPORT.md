# D491 / D474(C) experimental draft — NOT ADOPTED

Branch `codex/pv-c474-draft-20261029`, base `a9a9781f8a`. No merge, push, repin or adoption. This draft changes the host client only. Privacy target not yet established; no endpoint premise removed. The complete D159 observer and D478 timing obligation remain.

## Source design (validation pending)

A literal-only client error carrier replaces anyhow at the client boundary; all foreign errors are discarded without Debug/Display. A constant panic hook and a host-only abort profile replace default panic reporting. Startup disables and primes std's backtrace cache before input processing. getrandom 0.3.4's supported `linux_raw` backend is selected by the client build recipe, using inline-assembly getrandom(2), without dlsym or libc getrandom. The suggested `linux_getrandom` backend still calls libc::getrandom and therefore does not remove LD_PRELOAD interposition; this draft deliberately uses `linux_raw` instead.

Detailed evidence, changes, validation and costs will be appended below as gates complete.
