# R706: extra active-column witness

Exact focused target: `AspisV8R19/R706ExtraActiveColumn.lean`.
Source revision: `905924ec07abbfc01f1f7f21fb189375ecff57b1`. Source SHA256: `c1a0dc8612efde831dc15a2f86ef7f167ec543424be511e2d0c38bbad94fa952`. Final run `1791127814991973000`: exit 0, wall 0:02.72, Lean-child RSS 3466788 KiB, swap 0.

The proof defines the alpha-one extra quotient column with values `q[1018]=1`, `q[1016]=-1`, and zero elsewhere. It proves all high active coordinates see zero, using the exact block-254 active-slot theorem (slots 1 or 3); records preceding active code 1019 at selected column 698; and proves the scalar source chord `(2,0,0)` vanishes on every high active row. The top four quotient entries are zero.

The proof is a finite-layout/source-shaped algebra fact. It does not prove an active 214-minor rank or determinant, the normalized-circle restriction, native execution, H1 image coverage, legal target compatibility, a simulator, privacy, or security.

The initial changed draft failure and final full receipts/logs/source snapshots are retained. All five final `#print axioms` reports are standard subsets of `propext`, `Classical.choice`, and `Quot.sound`. No unchanged successful check was rerun.
