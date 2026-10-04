# R698: selected active-core layout

Exact focused target: `AspisV8R19/R698ActiveCoreLayout.lean`.
Source revision: `6260dc41cff6bc0216706d188ecd1f11ee80124c`.
Source SHA256: `3f83f705d9d7bcba59b4bef4407027cfa5f964578c5a474bee86312e295f10f3`.
Final run `1791126090242392000`: exit 0, wall 0:26.66, Lean-child RSS 4383900 KiB, swap 0.
Pinned Lean 4.32 `-j1 -M4500`; systemd `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`.

This formalizes the finite selected TwoSwap routing layout only. It proves 214 active source coordinates, 213 active coordinates below source index 1020, and the sole remaining active source coordinate 1022. Every high four-slot block omits a slot. The defined selected columns are injective and lie below 699. At block 254 the active slots are 1 and 3, so the additional column 697, corresponding to local slot 2 / quotient coordinate 1018, is absent.

The zero-slot selection proof uses `high_block_not_full` symbolically: when the three lower slots are active, the fourth is excluded by the finite layout theorem. The top-column proof uses the exact block-254 1-or-3 fact. It does not assert a matrix rank, determinant, normalized-circle condition, source execution correspondence, or any privacy conclusion.

All ten attempts are retained. The first nine are rejected changed drafts: finite-decision recursion and dependent `Fin`/Boolean proof-shape errors. The final attempt is green. The final seven `#print axioms` reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The rejected after-base permutation inventory is retained separately from the corrected before-base layout inventory.

Boundary: this is a source-table/model layout fact. It does not prove the required 214-column minor, the normalized-circle parameter condition, or actual selected-source H1 image coverage. Those gates, then legal C1/H1 target compatibility and the causal shared-oracle simulator/loss analysis, remain open. Genuine verifier measurements 999,790 / 999,532 CU and every security parameter are unchanged.
