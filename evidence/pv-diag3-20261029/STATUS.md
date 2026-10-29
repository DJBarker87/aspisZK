# D443 diagnostic execution refinement

Worktree `/Users/dominic/ZK/.worktrees/pv-diag`, branch `codex/pv-diag3-20261029`, base `344a81b9f0`. Budget: 100 Lean attempts (64100–64199, audits 64197–64199), at most 40 native scopes, no Kani. Frozen crates/programs, observer, simulator and T are unchanged.

Order: native error-path leaf/ownership/capture/write refinement under own-1; joint L1 law consuming existing count laws; composition at the actual client observer. Native association is source binding, with V370 retained. External influences are classified under own-2''' rather than assumed absent. All normal, panic, abort and divergent-prefix effects must survive; unwind cleanup applies only when the runtime unwinds.

The global privacy target remains unestablished. Existing exclusions and count-law evidence are reused from diag2; new conditional operational lemmas are not whole-native or whole-privacy claims.
