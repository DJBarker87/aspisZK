# Lean composition reduction diagnosis

All attempts used -M7000 and the same 6G high / 8G max / swap0 / Tasks64 scopes. No cap was increased. L042, L047, L048, L050, L051 and L052 were rejected for kernel excessive memory consumption; they are excluded. The failed diagnostics' self/sorryAx lines are not accepted axiom audits.

The original concrete composition expanded array-copy back-functions and tuple continuations into the large arithmetic Result expression. Splitting the prefix proved its generic bind/source laws (L046), but direct concrete tuple beta reduction still forced the reference computation. L052 isolated the remaining failing declaration: arithmetic transport passed; tuple_beta hit the memory limit.

The permanent replacement is `NDD_TupleContinuation`: curry/uncurry and pure-tuple bind laws are proved on arbitrary continuations, where no concrete computation can unfold. `NDD_PackArithmetic` applies those named laws instead of reducing the concrete reference. The concrete prefix is packaged with already-proved bind/source equations, not assumed equations. The checked opaque value introduces no axiom; its source theorem prints only standard axioms.

L053 generic tuple laws PASS, L054 arithmetic/tuple transport PASS, L055 prefix/reference composition PASS (1.2842701419722289 s, 2635936 KiB RSS, swap0). The source-to-prefix equation and arithmetic-to-reference equation are checked separately. This is model-side composition and does not discharge the remaining native SAME-execution association. L056 jointly audits all 45 new top theorems and has only standard axioms.
