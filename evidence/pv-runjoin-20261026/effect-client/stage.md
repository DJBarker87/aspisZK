Effect-aware continuation from 55749bbc7f (2026-10-26).

Budget: 50 Lean, 10 Kani unused at entry. Attempt 20950 passed (2.40s,
4282332 KiB RSS, swap0, standard axioms). No implementation/source pin change.
The source snapshot in receipt-20950 includes redundant instance binders;
the working successor removes those binders before dependent compilation.

Admission 20951 refused at 12:14:35.347618 UTC: reserved51942260736 +
requested8589934592 > safe59055800320 bytes. No compile launched; zero budget
charged. Retry not before12:17:35.347618 UTC, with next ID20952. The existing
reservation script and launcher are unchanged. Receipt copied after retry.

PV_RunJoin_EffectClient interprets actual factored entropy continuations and
calls the ACTUAL emitted prove_masked_attempt at S2. It has a shared world,
mutable policy and durable store; only Rejected retries. Source/native effect
adequacy and full observation decoding are NOT proved by this definition.

V329 E1 is ONLY a conditional successful64 law; uniform counting of error tags
is not implied. The predecessor RawTape mixes bytes and optional errors.
No assertion of uniform native RawTape law will be introduced. The native
conditioning and tape-coordinate installation remain V336/V339 and V037.

20952: corrected duplicate binders, pass5.13s,4281676KiB RSS,swap0.
20953: new EffectPaths rejected on ambiguous opened `attempt`/`run`/`Secret`
names; successor narrows namespace opens. Compiler's error recovery prints
sorryAx for rejected declarations; no such object is accepted as evidence.
20954: admission refused12:18:45.845328UTC at same48.375GiB reservation.
20955: read-only admission was checked prematurely12:20:29UTC and allowed;
NO source transfer or scope launch followed. This check does NOT replace the
required180s wait. Next launch/admission not before12:21:45.845328UTC.
