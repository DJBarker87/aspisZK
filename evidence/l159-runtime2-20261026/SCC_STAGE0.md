# SCC stage 0: corrected physical association audit

Root: AspisR1.Rc5_Top.deployed. Only new SCC_ modules and this evidence directory may change. No shipped source change or ELF rebuild trigger.

Read root Security and proof discipline, r1p-common/local-lean, historical S2 handoff/plan/diagnosis/interface, both required C3 addenda, owner amendment, SCB handoff and all SCB modules, SInt2 handoff, Rc5 recount and actual root. Historical requested S2 paths resolve under docs/research/100bit-spend-path-20261013/.

Corrected L159 avoids virtual replay in the physical log. A different issue remains: Rc5's runtime, P, adversary/chooseSecond, and bank observations are independent binders. CPH records checkpoint bank actions, not a RunView of the account experiment. RuntimePersistence states only loaded data byte persistence. CPH_Recorder derives its own bank program's output, not the runtime/P association. DrvC's source takes fixed public/proof bytes and the saved TX1 checkpoint; GExq's second submission remains adaptive.

Next focused diagnostic: derive the stored-input projection necessary for the first-pass equality, and exhibit an accepted, mismatching runtime for any fixed source/P/H. Preserve arbitrary already satisfied runtime-independent conditions explicitly. This is an interface obstruction, not a deployed attack. If confirmed, the explicit stop exception applies: do not add runtime/source association as trust or wrap the old top as SCC_Top.

0 Lean / 0 Kani. Host objects and unchanged S2W launchers will be reused, one scope at a time with -M7000, 6G/8G/Swap0/64 tasks. No full replay.
