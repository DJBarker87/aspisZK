# Excluded attempts

L002: inspection used unknown U8.toBitVec/U8.val; actual carrier is UScalar.bv. No theorem.

L003: clipped column68 indentation causes Lean errors and recovery sorryAx; excluded completely. L004 uses token-identical repaired whitespace and no axioms.

E002: actual frozen require_zero cannot emit under pinned Aeneas: Not_found in InterpLoops loop-context join. No native result. No retry; extraction2/2.

Resume failures: L031 Vec.deref carrier reduction (fixed L033); L034 nonexistent Option.toExcept (fixed L035); L037 tactic alternative parser and L038 recursive macro declaration order (fixed L039). All failed outputs, including recovery sorryAx, are excluded. These are elaboration repairs; no timeout/memory failure was rerun.

Registry decomposition failures: L149 missing import, repaired L150. L155–L157/L159 generic higher-order protocol fusion did not elaborate; retired in favor of direct source factoring (L160/L161). L164 data projection did not reduce under the case equation; explicit carrier equation repaired L166. L172 failed aggregate Boolean rfl; L173 broad apply_ite/or simp recursed, retired. Small symbolic Boolean law L174 and explicitly staged reduction repaired L176. L175 lacked the guard normalization; excluded. L180 dependent conv rewrite and L181 unconstrained apply_ite rewrite failed; repair narrows to a standalone simp step. L182 PDA protocol inference failed before application; explicit installed call is the replacement. Failed compiler recovery axioms are never evidence of a theorem.

L183 standalone apply_ite simplified the whole equality; retired this shape and used finite symbolic ten-Boolean law L184, yielding L185. L186 generic PDA protocol inference and L187 explicit higher-order application still failed conversion; generic fusion retired. L189 exposed seed expressions under a common Env case but did not close; L190 had tactic sequencing syntax errors. L191 unfolds only the seed constructors before the Env case and closes both outcomes, replacing these failed shapes. No cap, timeout, or recursion option was increased. L194/L195 TX1 returned bind confused its fixed continuation value with a universal argument; replaced by the fixed same-call value (L196 submission).
