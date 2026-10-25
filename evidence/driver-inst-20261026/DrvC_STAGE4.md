# Stage 4: both complete stage oracle programs

DrvC_FirstProgram.interpreted now proves complete Program equality for TX1,
with only the nominal current-to-Port1 Error transport at the returned value.
DrvC_PairProgram.stages composes that equality and DrvC_SecondProgram.program:
the literal Port1 two-stage tree equals the installed two-call source program,
including all outcomes, query order, duplicates, rejected prefixes and the
same actual returned checkpoint consumed in TX2. No semantic-compatibility
hypothesis, chosen trace, acceptance or desired conclusion is assumed.

The configuration used here fixes actual release library leaves through
DrvC_FirstConstants.configuration (literal Port1 library bodies/std semantics).
It leaves every protocol body/SDK datum of the original Configuration intact.
CurrentCaller already installs its own extracted constants. FirstConstants
only proves tiny scalar offsets using checked arithmetic; no recurrence/large
array/kernel fixture evaluation was performed.

048 hit deterministic 200000-heartbeat timeout (14.7013s,5459536KiB,swap0).
It was replaced, never retried unchanged: named source/typed suffixes in
FirstSyntax (050), suffix Program proof (054), prefix syntax (056), original
whole syntax bridge (059), prefix Program proof (058), composed whole Program
proof (060), two-stage Program proof (061). Replacement targets remain small.
New supporting pure/query/prepare/mutable laws pass 037/038/041/044/045/046/
047/052. Their #print axioms are standard only. All earlier failing versions
are excluded and their full logs retained. 055 was a local text-generation
failure followed by a missing-config launcher preflight; no Lean ran, and no
launcher/infrastructure was changed. Actual Lean count at 061 is 59 (006 and
055 did not launch Lean), Kani 0/0. Count cap remains 100 actual Lean attempts.

L160 still awaits the physical raw-byte entry/native accepted-pair association
and successful fixture/non-vacuity integration; no ledger credit yet. L157,
L159 and existing named trust/runtime/extraction/other-cone items unchanged.
No shipped file or key changed, no package replay or runtime regression rerun.
