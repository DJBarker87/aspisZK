# Transport route after the checked obstruction

The event is NOT an unordered collision-pair predicate. It is
hitsBad (AllAddressCollision.bad iv pred Q) emptyTable log, with freshness
checked at that occurrence. AllAddressCollision.bad also checks a Small table
cover. Therefore neither equal answer functions nor sublist inclusion
justifies the requested implication. SCJ_Projection.event_implies_refuted is
a direct negation at release iv and Q+2965.

Two candidate sufficient repairs are being checked, without assuming them
on actual accounts:
1. SCJ_Alignment.Aligned records every retained projected cache miss as a
   full cache miss, with table-value extension and full budget coverage;
   arbitrary extra first reads may be deleted if they preserve this invariant.
2. SCJ_Projection.event_implies derives transport from membership plus
   preservation of first-occurrence order on projected addresses. Consistency
   and full first-read budget derive the local covers and table inclusion.
   SCJ_AccountProjection.event_implies specialises this to actual F3X/SCE
   recorders and SCF_Charge, retaining EXACTLY Q0+Q1+2965 and no extra loss.

The remaining read/order inputs are proof obligations, not new trust items or
premise-removal credit. Arbitrary selectors are not identified: actual replay
and physical audit selection still need their same-witness indices.

SCI_Recovery.account_of_join also has an explicit chronological `ordered`
input. The repaired collision implication alone does not prove it. The weaker
SCF_Recovery.agreement interface can instead consume exact semantic public,
three recovered-frame and three causal-cut equalities, which must likewise be
established on the physical account. No whole-log equality is assumed true
merely from the collision implication.
