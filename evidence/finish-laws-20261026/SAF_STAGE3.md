# Stage 3: three saved Prepared identities

SAF_FinalTop.deployed compiles in SAF_020, standard axioms only. This preserves
all outer Rc3 binders and same witnesses/conclusions while additionally deriving
PairingLaws.claim/alpha0/alpha1. The old caller facts give checkpoint identity
at reached TX2; the actual installed op18 return plus the already-derived saved
Vec encoding supplies BodyMatches. SAF_SavedIdentities proves the decoder
roundtrip before specializing the literal Context, avoiding large normalization.
SAF_ReducedLaws.Arithmetic retains EXACTLY the seven original arithmetic fields
at the SAME Prepared and dictionary; no quantified law was strengthened.

SAF_009 hit default-heartbeat timeouts (39.23s); it was split into generic
saved-field interpretation (SAF_010) and Context specialization (SAF_012).
SAF_011 needed explicit ite_true; SAF_014 used reserved token matches. Both
are excluded development failures; their changed replacements pass. No limits
were raised and no failed source was rerun unchanged.

Delta from Rc3: 15 return families + L139/L140/L141 =18P removed.
Actual82T+113P →82T+95P; Session A92→74. Assigned31→13 still open.
SAF_020: exit0,5.908458996s,5376216KiB peakRSS,swap0.20 actual Lean
invocations:16 passes,4 excluded failures;0 Kani. Further canonicality work
will reuse this green predecessor, not replay it unchanged.
