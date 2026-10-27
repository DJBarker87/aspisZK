# Raw push proof method

The native IteratorRange.next calls do not reduce definitionally. PushStep
uses their existing exact specifications to identify the five iterator states,
then exposes each of the four fixed array updates and terminal return.
FoldPush composes those named step equations via the existing loop equation;
no kernel normalization of an unknown recurrence is used.

Historical039..043 retain the failed rewrite/definitional experiments;
044 proves all five iterator and body equations. 045's final simp already
closed the goal, so the trailing rfl was rejected. 046 removes it. Final
passing receipts determine acceptance; rejected attempts get no credit.

The prepared Raw00..Raw32 modules isolate the two canonical raw products for
each of the three pushes at each of four slots. They are uncredited until
compiled; final validation/handoff will enumerate the accepted exact hashes.

All twelve complete actual pushes now pass: Raw00(068), Raw01(069), Raw02(071),
Raw10..Raw32(072..080). Their24 dense canonical products and exact after-state
arrays/counts are checked. The generator emits the verified array-map/raw
lemmas, named FoldPush steps, checked-Q and exact counter increment permanently.
065/066/067's nominal unfolding/counter/extra-tactic rejections are retained.
No raw-pairing value remains chosen or assumed at query0. Finish and final
addition still need their own passing receipts; no query equality is claimed
by this stage. All accepted axioms are standard.
