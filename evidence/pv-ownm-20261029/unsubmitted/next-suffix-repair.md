Uncompiled proposal only; no credit and no further development attempt remains.

65996 fails at `rw [htlen] at hd`: dependent occurrences in the hidden
getElem/Fin proof still contain `hi : i.val < (point.drop w).length`, so the
rewrite motive is ill typed. The accepted high/low row-bit and fold transports
do not depend on this draft.

Next focused repair: rewrite only the RHS of hd after the getElem_drop step,
for example `conv_rhs at hd => rw [htlen]`, rather than rewriting every hidden
dependent occurrence. Alternatively first restate hd with the explicit
`point[w+i.val]'hb` LHS and an explicit natural RHS index, then rewrite only
the natural RHS. Recompile this smallest draft before crediting source_dense,
concrete_source_dense or concrete_restore. No counterexample is inferred from
the failed proof. All theorem reports containing sorryAx are uncredited.
