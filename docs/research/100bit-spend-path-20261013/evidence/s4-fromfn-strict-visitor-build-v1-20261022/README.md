# Strict TTraitType matcher build evidence

This packet records one cached build of the strict visitor candidate and the
setup failures preceding it. It does not include binaries or assert a semantic
repair to the from_fn loop.

The candidate Aeneas source is `source/InterpMatchCtxs.v3.ml`, SHA-256
`0d2ab7873780feaea346facc38f5429144153f6e93a08aef636509505216bb18`; its
associated interpreter source is unchanged at SHA-256
`1f1b6527bce296728cce288648e6b5f6aa4fd0f1387a06af33fee2642244b616`. The
source tree is the isolated v3 tool copy at
`/home/dombarker/project-offloads/d18-aeneas-reborrow-v1-20261022/aeneas-trait-guard-v3`.

The first three attempts are preserved as setup-only failures. The initial
systemd cap did not constrain the Docker child (`memory.high=max`); adding
Docker `--memory-reservation` still left `memory.high=max`; adding a gated
container and setting its owned scope's high and max limits exposed that
Docker's own swap file remained `max`. None reached `dune`. The fourth attempt
set all three limits directly on the verified owned Docker scope and released
the build gate only after checking its full ID, host PID, `/proc/PID/cgroup`,
systemd `ControlGroup`, and the cgroup's `memory.high`, `memory.max`, and
`memory.swap.max`.

The fourth build ran `dune build --profile release -j 1 main.exe`, exit 0,
9.53 seconds, peak RSS 502,568 KiB, swap 0. The output binary changed from
`f0eff7e5b2d638aa0611de64a2dc699e805ad0168f1ef42d5500c23a18a1aecc` to
`8b068c351f82a3a175d9907eece9228872d1165d82ff9380873afccfc10808d9`. The
original runner raised a Python `TypeError` while collecting `docker logs`
after `docker wait`; the exact build's GNU `time` record reports exit 0. The
receipt is therefore labeled reconstructed and notes that no post-run cgroup
snapshot was saved. The cached build was not repeated.

`check_packet.py` checks the source and raw run pins. This is only the strict
matcher build. It is not an Aeneas translation run and does not close the
source or semantic correspondence to frozen SBF Rust 1.89. A later Aeneas run
must use the separate guard-only LLBC output with MaybeUninit opaque, pin its
exact hash, and use the same verified gated-container method.
