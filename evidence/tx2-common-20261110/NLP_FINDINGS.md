# NLP findings (work in progress)

Target not yet established. No row promotion.

## F1: additional checkpoint/proof root provenance

NLP_RootDomain.kind0_fixed/necessary/mismatch (L007) show NLN's first-root binding cannot be repaired by selecting Parsed.semantic: wire fixes committedRoot0 from proof[16..48]. NLP_ResumeRoots.returned (L008) shows the SAME resumed Prepared roots read checkpoint[112..144] and checkpoint[144..176]. Frozen verifier.rs:393–431 checks proof/public/checkpoint digests, field codecs, query range and final cursor, but does not compare either saved root to proof root bytes. Frozen candidate.rs:294–303 checks split and reads folded_root; it does not supply that equality either. These source facts do not establish a deployed counterexample or failure of soundness.

The two expected input extents alone have not discharged this root binding. NLP_InputDomain.Root0 states the missing relation solely on original checkpoint/proof arguments (bf(2)); no child output, success, or row conclusion occurs. Its provenance at TX2:064 remains OPEN. It is not silently added to a positive root. Independent root1/folded-root and native fold installation work continues. A RuntimePersistence data-only law does not by itself assert what the checkpoint writer stored; no new runtime trust is proposed.

## Elaboration diagnostics

L001: implicit Type binder in the concrete polymorphic Native lambda was omitted; changed source passed L002. L005: ite simplification did not close the literal kind0 branch; changed source passed L007. L006: list-index reductions omitted; changed source passed L008. L009: rewrite required an explicit replicate-prefix length; under repair. Failed elaborations and any generated sorryAx diagnostics are retained and excluded from selected proof credit.
