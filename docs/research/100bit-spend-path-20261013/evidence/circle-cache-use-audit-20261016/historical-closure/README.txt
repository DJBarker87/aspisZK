Historical Circle source/import correspondence: completed read/hash audit

The exact rejected object39ea3fa6… belongs to the historical broad-import source
867bb6d9…, not current focused-import source70b2727f…. The retained producing
Lake trace matches both recomputed source and output hashes. Its Lean4.32.0
commit8c9756b… matches the current host/runtime version. After removing only the
import prefix, the11,530-byte declaration/proof body is byte-identical; this is
source-body equality, not a newly proved equality of elaborated terms.

The original setup enumerates exactly8,639 package modules/34,556 artifacts.
Every actual artifact Lake hash now matches its retained producing trace output.
Fresh SHA256 of all5,937,032,064 bytes is identical between the local original
cache and host imported cache; no file is missing. The exact ordered Lake fold
(including duplicate imports) reproduces historical Mathlib legacy693e25ff4498b2e4
and all-artifactsf90ecd83c52e54ec. Both scanner attempts are retained. Hash check:
exit0,2.767s,1,590,908KiB process high-water,341,159,936B cgroup,zero swaps.
No theorem/dependency replay occurred. All27 archive member hashes were checked
locally; archive-members.json is authoritative if the member count changes.

Minimal repair: retain original receipt/manifest bytes and attach the explicit
historical-source-mapping.json correction. The unchanged object then has an exact
historical source/import correspondence. The Circle-specific concern does not
require replaying177 source-graph descendants. This does not newly attest the
producing sources of all174 other retained predecessors or call the old object
a current focused-header build. The separate sampler already uses its checked
current-source replacement and is unaffected by this retrospective correction.

The independent24-project framing-header audit found no hidden project import
or Circle. Every compiled import set matches its retained source set (duplicate
implicit Init only). Header matching is not a producing-source receipt; in
particular old UniformStateFirstHit bytes must not be relabelled as the new live
proof repair. Detailed paths/hashes/header logs are included for workerA.
