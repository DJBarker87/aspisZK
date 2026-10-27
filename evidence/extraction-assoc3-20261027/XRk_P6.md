# Per-iteration Kani evidence

10/10 allowance used. XRk_K001 and K002: TIMEOUT at CBMC 90s, sparse WideExact
coordinate x and base-field scalar y both arbitrary canonical 31-bit values.
No unchanged retry. Starting K003, x is restricted to {0,1}; y remains arbitrary
canonical. This isolates the source EbyKDot push against generic WideExact
mul_qm31 without the expensive multiplication identity in the original shape.

K003..K008 PASS: coordinates 2..7 respectively, one nonzero coordinate, x in
{0,1}, y<P. Each proves successful single push and equality of finished state to
mul_qm31, and covers x!=0 && y!=0. Coordinates0/1 have no new passing result.
K009/K010 PASS: malformed scalar limb0/limb3 respectively, arbitrary x>=P;
source push rejects and the finished initially zero accumulator is unchanged.
Both cover x=0xffffffff. No 29/4096-step fold, generic field algebra, arbitrary
accumulator history, whole prepared_claim, source extraction association or P6
bridge is established. All twelve full leaf bridges stay OPEN.

Cargo dev profile is optimized (opt-level3/debug0/overflow-checks=true), one
compiler job; timing is compilation then one named single-push SAT check.
All ten receipts include the cgroup caps, revision, exact argv, source hashes,
wall/RSS/swap and complete stdout. Input snapshots include both original and
reduced source versions, with source hash verification in XRk verification.
No shipped cfg(kani) module changed: these are standalone harnesses importing
the pinned crate at revision 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
