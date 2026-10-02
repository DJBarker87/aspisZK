# Prior saved-evidence checker

This is the exact checker version used for the initial R346 saved-evidence audit, preserved before the reusable checker was introduced. SHA-256: `973814a78ea1f0d65bc91c00f7937b942ea1a03de1e68908ee14db18fa76ae5e`.

Its compile-time result remains in the parent evidence directory as `saved-evidence-audit.json`. The current checker reads from the archived staging bundle, checks the receipt revision is an ancestor of the current revision, and writes any later recheck output only under `.r21-scratch/`.
