# Recursive proof normalization review

44335 (PV_Canon_Rounds) failed at the Lean kernel -M7000 limit: exit 1,
65.19 s, peak RSS 7,177,732 KiB, swap 0. The proof instantiated the complete
closed current dictionary inside the induction, duplicating normalization
work. A read-only monitor observed 6,941,976 KiB at 50 s; the attempt to send
TERM arrived after Lean had already exited. No cap was raised and no unchanged
rerun is authorized.

Replacement: PV_Canon_RoundsGeneric proves the recursive transport with the
ExternalFuns dictionary as an opaque variable and a one-round equality law.
PV_Canon_Rounds then instantiates that theorem once with the already-proved
current one-round law. The base branch is kernel reflexivity, not broad simp.
This isolates the induction from the large closed dictionary and keeps the
same quantified caller/Result statement. Compile the generic predecessor first.

44341 rejected the generic proof at the default heartbeat limit while reducing
the terminal branch. 44352 changed the rewrite to target the left/right roots
explicitly, but its kernel check still reached -M7000 (exit 1). This invalidates
the proposed normalization fix as a completed proof. The recursive transport
and current wrapper are archived as unsubmitted drafts. The checked one-round
transport and exact successful-prefix theorem remain accepted. No full
recursive caller equation is credited. The small RoundVisit control invariant
is explicitly a model until associated with the actual recursive Result body.
