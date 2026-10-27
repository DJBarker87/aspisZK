# Adopted installation finding — branch (b)

Target not yet established. The adopted theorem is `AspisR1.ARX_Root.deployed`.
Its binder is `(c : DrvC_Installation.Configuration FIo_Install.W CoreError)`.
The selected dictionary is `FIp_Install.configuration indexError c reservation`.
`FIp_Install.slots` and imported `FJn_InstallationBoundary.adopted` give
`(FIp_Install.configuration indexError c reservation).boundaries.terminal = c.boundaries.terminal`.
This is definitional equality: neither FIp's selection nor Rc5 overrides it.
The finishOwners binder is `FIp_GlobalOwners.Owners` of this dictionary and
`(Rc2_Install.configuration (Rc5_Install.seed indexError (FIp_Install.select reservation c)) reservation).boundaries`.
No binder fixes `c.boundaries.terminal` to the extracted body.

By contrast `FIq_Install.configuration` calls FIp on `FIq_Install.seed c`,
which explicitly installs `FIq_Terminal.terminal`. This is the separate FIr
path. `FJn_InstallationSeparation.not_uniform` constructs an allowed choice of
c with a terminal distinct from FIq's, using two tiny distinct constant outputs.
This proves the requested uniform FJq_TerminalInstall equality is false;
it is not a forged accepted execution or a cryptographic counterexample.

Consequently the installed FIq VALUE theorem cannot justify removing native
L146 / F3Y_G_L146 from the adopted arbitrary-callback statement. We STOP that
branch and do not silently specialize c. The literal transport remains useful
independently and is the continuation for this job.

Minimal proposed statement change: add an explicit equality
`c.boundaries.terminal = FIq_Terminal.terminal`, or select the FIq installation
consistently in every occurrence of the configuration, derived runtime,
extraction and owner interfaces. The latter requires a full dependency join;
either changes the adopted statement and needs lead/owner adoption. The
equality alone does not prove the remaining literal transport obligations.
Neither proposal is installed here.

Before/after: adopted theorem unchanged, all binders and conclusion identical.
Ledger method inherited from FJn: actual 83T/11P/13G, combined excluding alias
89T/14P/13G; removed=[], added=[], delta 0T/0P/0G/0C. Both L146 rows retained.
Non-vacuity is the inherited conditional fixture only; constant-callback
separation is an installation witness, not full joint release inhabitance.
