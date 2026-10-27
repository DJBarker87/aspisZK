# XRj release external definitions and association

Target not yet established. No generated file is edited. Local source files
use XRj_; only on the host, the compiler input paths supply the exact module
names imported by the unmodified pinned XRh release. Those isolated objects
are outside all shared LEAN_PATHs. No other worker files are changed.

Current branch is codex/cx-extraction-assoc2-20261027 (as provisioned), rather
than the older 20261026 branch label in the initial request. Budget this round:
100 Lean, 10 Kani, zero extraction. One capped scope at a time, -M7000.
All twelve leaf P6 bridges stay OPEN until proved; definitions are not bridges.
