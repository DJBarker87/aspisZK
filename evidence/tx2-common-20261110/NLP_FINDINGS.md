# NLP findings (work in progress)

Target not yet established. No row promotion.

## F1: additional checkpoint/proof root provenance

NLP_RootDomain.kind0_fixed/necessary/mismatch (L007) show NLN's first-root binding cannot be repaired by selecting Parsed.semantic: wire fixes committedRoot0 from proof[16..48]. NLP_ResumeRoots.returned (L008) shows the SAME resumed Prepared roots read checkpoint[112..144] and checkpoint[144..176]. Frozen verifier.rs:393–431 checks proof/public/checkpoint digests, field codecs, query range and final cursor, but does not compare either saved root to proof root bytes. Frozen candidate.rs:294–303 checks split and reads folded_root; it does not supply that equality either. These source facts do not establish a deployed counterexample or failure of soundness.

The two expected input extents alone have not discharged this root binding. NLP_InputDomain.Root0 states the missing relation solely on original checkpoint/proof arguments (bf(2)); no child output, success, or row conclusion occurs. Its provenance at TX2:064 remains OPEN. It is not silently added to a positive root. Independent root1/folded-root and native fold installation work continues. A RuntimePersistence data-only law does not by itself assert what the checkpoint writer stored; no new runtime trust is proposed.

## Elaboration diagnostics

L001: implicit Type binder in the concrete polymorphic Native lambda was omitted; changed source passed L002. L005: ite simplification did not close the literal kind0 branch; changed source passed L007. L006: list-index reductions omitted; changed source passed L008. L009: rewrite required an explicit replicate-prefix length; under repair. Failed elaborations and any generated sorryAx diagnostics are retained and excluded from selected proof credit.

## F2: C04 fold transport requested a stronger domain than its actual call

NLB_Parent.native_fold's merkleReply quantifies over every root after MerkleDomain has fixed only proof/resumed Prepared/split. NLN requires that the third root is bound to the current proof. The old universal-root premise therefore cannot be instantiated verbatim from NLN. NLP_TransportDomain.at_branch (L039) and NLP_EnteredTransport.source (L040) retain the actual checked folded-root projection and prove the same rejection/ordered-occurrence transport on this narrower, caller-established domain. These are auxiliary transport lemmas, not a new row root.

L038 hit the default200000-heartbeat limit at broad constructor search inside the nine-site body. That shape is retired. The replacement isolates the entire domain construction in L039 and the parent only applies it at the actual branch in L040. No heartbeat/cap/timeout increase or unchanged retry.

Additional diagnostics retained/excluded: L010 missing namespace on a range lemma (L012 passes); L011 ambiguous Byte (L013 passes); L014 run-name ambiguity and L016/L018/L020/L022/L024 existential/tactic quotation/name diagnostics (the small SAME range/copy/unwrap proof passes L026); L021 Event-name ambiguity (L023 passes); L025 numerical-carrier simplification (L032 passes); L033 reserved parser tokens (L035 passes). All selected modules are pinned to passing source snapshots in NLP_MODULES.json.
