# NBA stage 2: native prefix and exact cohort replay

NBA_K004 PASS: actual frozen Prepared::new on S2-shaped live buffers,
all scalar return bit patterns/states, exact rows/nonzero flag, same y1,
all inactive-byte positions, round0 pointer/length, every root+round1
concatenation position, and final-message query pointer/length.
The terminal query stub records a reachable cover before assume(false),
so this is prefix-only evidence. No returned prepare result is credited.

NBA_K003 timed out (104.542s,2017128KiB,swap0); split at query.
NBA_K005 excludes prefix payload comparisons but still times out
(98.637s,1933764KiB,swap0); next split is the exact source suffix.
Neither timed-out shape is rerun unchanged; no cap/timeout increase.
No own external-sat/smt solver files were found in NBA_tmp after K003.

NBA_L008 checks the converse cohort trace replay and full output/scratch
uniqueness. It consumes concrete SAME per-call observations, not a supplied
whole prepare result. It does not itself construct native observations.
Rejected drafts L004-L007 and their sorryAx recovery prints are excluded.
NBA_L009 checks native/cohort eight-word inverse and canonicality port.
All accepted theorem audits contain only standard axioms or none.

No XRn extraction-kit equality is applied by NBA modules. The inherited
CLOSED LPt proof's carrier-port dependency closure remains explicitly reused.
