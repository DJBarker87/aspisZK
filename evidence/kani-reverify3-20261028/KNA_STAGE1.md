# Initial focused inputs

K001/K002: actual Vec::from(array128), symbolic i=1..15, truncate(64+4*i), one append4, live-prefix and appended-byte checks. Both TIMEOUT; no credit. K003/K004 retain the identical prior solver configuration for the cap256/i17..21 pair.

Starting at the first 160-byte body window, new gates use installed Kissat with CBMC formula slicing. This affects only previously unrun windows and their matching controls. Later timeout replacements narrow byte domains; no unchanged timed-out gate is rerun. Both versions of the invocation gate are archived by SHA-256 in sources/.

The Lean generator emits named symbolic applications, a complete eleven-window-plus-tail partition, explicit half-window union laws, query capacity domains, exact original serializer byte projections, and nine original row models. It contains no large concrete recurrence normalization. These are models with separate runtime heap obligations, not automatic heap credit.

## Terminal interruption

K001–K014 all TIMEOUT. Local evidence recovery failed with ENOSPC during K014. K014 was recovered read-only; no resubmission. The five timed-out 160-byte prefix pairs have not been halved because launcher storage failed before any replacement launch. All Lean/native source preparations remain unrun. See KNA_FINDING.md for the authoritative terminal disposition and row-by-row budget-stop justification.
