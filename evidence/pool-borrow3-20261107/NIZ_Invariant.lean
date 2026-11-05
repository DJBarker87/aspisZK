import NIZ_Noop
import NIZ_AliasWindow
import NIZ_Dominance
import NIZ_SiteBounds
import NIZ_Groups
import NIZ_Cuts

/-! The deployed Pool-wide invariant is NOT instantiated here. NIZ_Noop.source_scope
is the empty callback MODEL run, backed by the capture-free literal's local
native packet; it is not any of the 13 original guard-owner ScopeRuns.
NIZ_OPEN_SITES.md identifies their exact missing source/callee/guard relations.
No conditional wrapper is presented as the missing actual source instance. -/
