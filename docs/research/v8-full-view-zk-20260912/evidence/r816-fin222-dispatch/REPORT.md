# R816 Fin222 active and supplementary dispatcher

For arbitrary `P : Fin 222 → Prop`, indexed facts over `Fin 214` at `activePos i = Fin.castLE ... i` and over `Fin 8` at `supplementPos j = 214 + j.val` imply `P r` for every `r : Fin 222`. The proof splits on `r.val < 214`, transports the active value with `Fin.ext`, and in the complement derives `r.val - 214 < 8` then transports the supplement value with `Fin.ext`.

The theorem is pure finite-index logic; it states no matrix or verifier fact. Successful full axiom output is recorded in the receipt (`[propext]`). The initial unsupported Omega import and the first arithmetic-lemma application error are preserved as failed attempts.
