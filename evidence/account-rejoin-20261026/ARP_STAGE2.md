# ARP stage 2: exact fixture composition stop

The requested accepted same-run fixture does not compose with the SAME SCE
native witnesses. This is now a theorem, not merely a missing inhabitant:

    ARP_SameRun.fixture_not_extracted ops hashv :
      Not (S2W_DigestExtraction.AeneasExtraction ops
        SCE_FixtureData.n1 SCE_FixtureData.n2 hashv)

It holds for EVERY ops/hashv, hence in particular for BOTH dictionary carriers:
F3S_Join.accepted_log_eq's SdkD_PairBatches.dictionary and Rc9_Top.deployed's
DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation).
Both exact signatures are freshly checked in ARP_005/stdout.log.
The conflicting field is extraction.stage1, universally quantified over
program/accounts/data. SCE n1 is constantly Ok saved. On an empty account slice,
AdapterRw.Accepted.first_call would require a successful index at zero, which
is impossible. ARP_SourceBoundary.empty_accounts_reject proves that tiny source
fact symbolically, without running the cryptographic fixture or unfolding a
large numeral/recurrence. No native success can be substituted for this field.

ARP_SameRun.boundary_joint simultaneously retains the SAME approved game,
RuntimePersistence, both SCE local wrapper successes, and original real JFx
public/proof byte submission, alongside the negated extraction instance.
Thus the diagnosis is non-vacuous. It does NOT prove that accepted log equality
is false for the installed account, that the real bytes cannot be accepted by
real source functions, or that the entire Rc9 antecedent is inconsistent.
A new source-faithful fixture on those bytes is still possible; it requires
its own actual source acceptance and the same-witness bank support proof.
The inherited SCE_JointObserver.joint also has both runtime admissions and
SDK/std, but deliberately leaves installed account acceptance computed.

No ARP_Join or replacement deployed endpoint is built. The explicit phase-1
instruction says to report the exact mismatch and STOP if (2) does not compose;
that gate takes precedence over using the remaining compile budget. This is
not budget exhaustion. The generic all-world bank factory in stage 1 is also
unproved; BankSupported is a diagnostic definition, never a new top premise.

ARP_004 passes the generic empty-account lemma; ARP_005 passes SameRun and its
joint fixture/axioms plus checks F3S and actual Rc9 signatures. All audits have
only propext/Classical.choice/Quot.sound; all scopes 6G/8G/swap0/Tasks64,
-j1 -M7000, one at a time. No dependency build, cap change, timeout or memory
kill. Exact status/time/RSS/swap/source revision/hash/dependencies are retained.
