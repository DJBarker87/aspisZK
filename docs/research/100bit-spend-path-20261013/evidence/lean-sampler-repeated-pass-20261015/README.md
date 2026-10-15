# Repeated machine-word sampler pass

This bundle records the focused `R1SamplerRepeatedPass` build. It composes the existing bounded word-division pass with the natural-number low-digit model: for arbitrary `n` and word list, returned remainders equal `lowDigits P n (wordValue words)`, their positional value is the input rank modulo `P^n`, the residual word value is the quotient by `P^n`, and every remainder is canonical (< P).

This closes the mathematical repeated-pass connection for the supplied word model. It does not prove Rust array/index execution or identify the current Rust challenge sampler with this model.

The NUC run used the pinned snapshot runner, `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`; attempt a exited 0 in 0.82 s, peak RSS 1,769,336 KiB, swap 0. All four axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
