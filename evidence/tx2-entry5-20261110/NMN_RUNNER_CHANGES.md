# Owned runner changes

NMK runner copied read-only into NMN, renamed owned paths and fixed compiler budget60 (reserve2 final gates). Added Stream A cwd/cgroup count before each admission; count>=2 waits180s with a wait record. Shared reservation/launcher unchanged.

The dependency-current-source validator now skips non-module share/wait records via get(module); it still requires a successful current-hash direct-import compile. This is own-script maintenance under worker-script ruling, with unchanged validation strength.

Native gate remains the inherited strict frozen source/lock/dependency/feature validator with owned prefix/path substitutions only. No cargo-kani --locked flag; metadata --locked is retained, CARGO_NET_OFFLINE=true and post-run lock identity required.
