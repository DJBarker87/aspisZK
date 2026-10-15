# Independent review: SelectedOpeningData

I checked the packaged source, manifest pins, attempt receipt, axiom log, and object archive against the current worktree. The source snapshots and all four source pins match their declared hashes; the four archived objects match the member hashes. The sole attempt `R1SelectedOpeningData-a` records exit 0, 2.20 seconds, 3,573,720 KiB peak RSS, zero swap, and the 4G/6G/0 cgroup. Its five `#print axioms` reports list only `propext`, `Classical.choice`, and `Quot.sound`. The existing bundle checksum list passed before this review was added.

The mapping in `data` is explicit: `c0` is `row28`; `p0` is `OpeningPolynomialView.firstPolynomial row29`; `p1` is `secondPolynomial row30`; and `f` is `row31`. The six `Y` positions, as defined in `SelectedOpeningClaims.Y`, are the three point-claim vectors from row25, row25's extra vector, row26's `beforeZ1`, and row27's gamma payload. `W`, `V`, `F`, `F0`, `gamma`, `kappa`, `alpha0`, and `alpha1` are explicit arguments to the constructor; the module does not derive them from the payloads.

The `p0` and `p1` degree lemmas apply to any supplied payloads and give the stated bound `natDegree ≤ 6`; they introduce no coefficient-check premise. This is a typed model assembly and projection/degree interface. It does not establish transcript-to-payload correspondence, source recovery, or acceptance.
