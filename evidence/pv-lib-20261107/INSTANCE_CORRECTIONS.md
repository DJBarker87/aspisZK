# Instance interface correction, before consumption

Attempts49301..49304 compiled the four array adapters, but their draft `law`
compared entire machine states including nextActivation. D961/thread27 proves
that comparison invalid as an interface between summary and expanded runs.
No row used these instances. Their exact sources and receipts are retained in
superseded-sources/ and the host workspace. They are excluded from final roots.

Replacement: new Array*View modules export the graph of the provider's
deterministic result after `PV_LIB.view` abstracts the administrative counter
in every current/suspended store. Required cells, control, worlds and events
are retained. Numbering is a separate entry/machine invariant; no theorem
asserts that the zero in this canonical representative is a valid counter.
Array11View exports only the abort event prefix; its internal provider
equation is not a public post-abort state/frame contract. The specifications
remain unchanged. No provider source or CLOSED root was edited.
