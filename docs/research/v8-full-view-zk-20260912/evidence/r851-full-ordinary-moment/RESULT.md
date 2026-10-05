# R851 full indexed ordinary moment

`AspisV8R19.R851FullOrdinaryMoment.ordinary_moment_of_top_zero` proves that the complete 1024-coordinate contraction of `R738.rawOrdinaryWeight` with `R738.rawFlatten q` equals its three statement-point contractions, given explicit zeroes at flattened coordinates 1020 through 1023.

It reuses `R665FullSourceP2Boundary.full_flatten_pairing`; R788's marker and all three image updates are retained and eliminated only under the stated top-zero hypothesis. R793 supplies the marker's below-tail zero fact, and R740 gives each point transport pairing.

This is source-model algebra. It does not establish the top-zero premise from actual execution, legal-witness conditions, sampler/shared-oracle laws, or any privacy/security conclusion.

| Attempt | Result | Note |
|---|---|---|
| 1791162937443289000-d8042c1fcf77 | rejected | initial syntax/plumbing draft |
| 1791162956986053000-1b7ebcb14046 | rejected | branch-normalization plumbing |
| 1791162982521402000-27fd9234245a | rejected | finite-sum binder plumbing |
| 1791163000743541000-c3360cb30e6f | rejected | `rangeDot` exposure before point-pairing rewrite |
| 1791163017351240000-6f149a3cb6f6 | green | exit 0; wall 2.25s; RSS 3316120 KiB; swap 0 |

The final axiom output is exactly `propext`, `Classical.choice`, and `Quot.sound`.
