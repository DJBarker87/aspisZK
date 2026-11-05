# Excluded steps

L001/L002: API inspection queried absent names. Discovery errors, no closure credit.
L003: eight-word byte-read proof needed explicit lift normalization and finite-list conversion. L004 passes with the same mathematical statement.
L005: own Lean indentation error. L006 elaborated the proof and isolated the missing finite high-word cases; L007 supplies those cases and passes.
L009: own do-expression parentheses error; L010 then exposed an unnecessary tactic after solved goals; L011 passes after removing it.
L012: typed chunk constructor's attached-list projection needed definitional normalization; L013 passes.
L014: scan proof needed explicit typed get bounds and an error-carrier reduction before loop_done. L015 repaired these; its broad simp on the scalar port hit maximum recursion depth. L016 uses only the exact port equality and the single rejecting branch, with unchanged caps; passes. No depth limit was raised.
L018: parser substitution using broad congr reached deterministic heartbeat exhaustion (17.01652017980814 s, peak 5,919,736 KiB, swap 0). Tool limit in automatic congruence, not mismatch. Excluded; never rerun unchanged. NGV_Monad and L020 replace it with explicit bind-by-bind cuts. No heartbeat limit was raised.
L022: dependent match in validator totality required simp-only normalization before selecting the bounded error branch; L023 passes.

Audit setup's first reservation was allowed:false (projected reservations >55 GiB). No copy or build launched on that refusal. The own setup wrapper was repaired to preserve refusal receipts and implement 3-minute wait/retry, with unchanged reservation validation; retry 1 admitted. This is contention, not an infrastructure bypass.

L029/L031: parser-at child substitution needed explicit Option/tuple and addition cuts; local elaboration failures, no credit. L032/L033 exposed no-progress normalization tactics; L034 instead states the bind source explicitly and rewrites the two checked additions, then passes. L030 was an own-input preparation failure: attempted dependent upload could not resolve the not-yet-built NGV_AtSubstitution object. No compiler launched; reservation and transport records retained. It is conservatively charged one support slot, never presented as a solver result. L035 full packet passes.

## Semantic-expansion stage (all excluded failures resolved before closure)

L042/L043: range read/write proofs used dependent-if rewrites against an ordinary if. The asserted equality is the original selected window/lens; L044 fixes the rewrite form and passes. Own elaboration error, no semantic mismatch.
L045: packet-length statement used unsupported field notation for the parent namespace's after function; L046 names the function explicitly and passes. Own elaboration error.
L047: U8 iterator proof needed explicit end substitution and StepU8 normalization; L048 passes. Missing local scalar/iterator association, not a callee gap or source mismatch.
L049: missing whitespace made Lean parse the natural <= input expression as a different notation; L052 fixes it and proves both same-buffer frames. Own syntax error.
L050: broad simplification stopped at the tuple iterator cut before row_shape. L051 explicitly changes the bind source, substitutes the exact shape and passes. Missing local emitted-step association, no tool cap increase.
L053: low-row proof rewrote source pointer values before their width equalities and omitted one bind normalization. L054 orders those local equalities explicitly and passes. Missing local window/copy association, no source mismatch.
L055/L056: high-row proof redundantly requested a scalar bind already substituted; its replacement first lacked a result-type annotation. L057 normalizes the exact returned tuple and passes. Own elaboration errors; the full adopted callee law is NGV_ExpandAssociation.result, not a supplied successful child.
L061: finite-trace construction had a binder-spacing parse error; loop interpretation also needed an explicit typed state/body and normalization at the actual stop tuple. L062 constructs and interprets the full trace. Local elaboration/association errors, not a callee or source mismatch.
L063/L069/L070: initial-root association needed explicit irreversible constant unfolding plus scalar WP facts, prefix-range (rather than range) lens laws, and bind-by-bind reassociation through the tuple. L071 passes with every initial byte/cursor on the same buffer. Missing local entry association, not a tool capacity failure or source mismatch; no limits changed.
L064: prefix is a Lean keyword; L065 names the theorem preserved_prefix and passes. Own naming error.
L066: prefix-range mutable callback needed explicit subtype equality to the unchanged setter law. L067 supplies it and passes. Missing local lens equality, not native mismatch.

All remaining focused proofs L068 and L072..L074 and final raw/scan audit A003 pass. There is no unresolved failing assertion or missing assigned callee law. The only timeout was the excluded deterministic heartbeat limit in L018; there was no OS timeout or memory kill. No unchanged timed-out shape was rerun and no cap was raised. Failed elaborations' sorryAx diagnostic placeholders have no closure credit and are absent from the final raw roots.
