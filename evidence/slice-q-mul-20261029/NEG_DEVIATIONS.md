# Execution deviations

NEG_L001 (3.343 s, exit 0) was accidentally submitted while NEG_E001 extraction was active. Both were capped, but this violated the one-scope-per-job rule. No native/closure credit is claimed. Added an own-orchestration lock before any admission to prevent another overlap. This changes no lead infrastructure. The initial own runner also had an escaped-brace Python syntax error before any submission; corrected without weakening validation.
