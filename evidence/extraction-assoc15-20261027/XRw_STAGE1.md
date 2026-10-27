# Generic first-stop driver

The generic `XRw_GenericDriver.first_stop_fold` preserves the whole effect,
including any error and the exact selected state, through any finish
continuation. It is parametric in the stage function, state, index and effect
constructor (hence in its error carrier); its sole algebraic premise is pure/bind
left identity. The Aeneas Result instance will discharge this premise by reduction.
No stage totality or successful-output premise is assumed.

This is a generic composition tool, not the concrete eight-stage association.
The initial Except-only specialization passed L002; the broader constructor
version passed L004. Failed L001/L003 outputs receive no credit.

Before/after adopted headline unchanged: `AspisR1.RPx_Deployed.deployed`,
83T/0P/13G, L154 statement parameter. Ledger delta T0/P0/G0/C0. No premise
removed or trust added; A0-A8 remain OPEN. Generic non-vacuity: the stage may
return success or an arbitrary error; the theorem assumes no desired output.

Validation: exact command, source revision/hash, direct dependency hashes,
exit, wall, RSS, swap, scope limits and full axioms prints in L001-L004 receipts.
L004: exit 0, standard axioms only. Persistent cache absent on initial host
inspection; empty at creation. New and inherited objects are retained in the
owner-designated persistent cache; the final manifest will hash every object.
