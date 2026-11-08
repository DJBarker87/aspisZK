# TX1:094 prepare trace repair

L889 identified an instrumentation mismatch before candidate status. The old
NNG_Tree094.NNG_call_5 logged (public, proof, hash, observer, scratch), whereas
NNG_Events094.prepare matches the full tuple including the digest dictionary.
The old NNG_Producer094 therefore omitted preparation effects. It is not a
RowSpec094 candidate and must not be used as a full observed producer.

NNG_PrepareTree094 replaces only that lexical prefix with a call recording
(digest, public, proof, hash, observer, scratch). The source function, child
arguments/results, and checked suffixes are unchanged. NNG_ErasePrepareTree094
proves each prefix erases to the SAME fresh NMT emitted body; L908 passes,
standard axioms only. NNG_ProducerFull094 supplies the corrected producer.
Passing suffix folds still use the identical NNG_Producer094.port, which maps
only native return values and is independent of the corrected trace prefix.
No frozen source, RowSpec, child law, runtime trust item, or VLib field changed.

Constant arithmetic: broad unfolded offset normalization was retired after
recursion-depth failures. NNG_ScalarOps094 supplies generic checked operations;
NNG_CompactBase094 and NNG_CompactConstants094 prove named source constants.
The 16*426 multiplication uses commutativity and the subtraction uses omega,
so no long structural numeral reduction or raised recursion limit is needed.
The decomposition follows NMT_R2_ConstantsA/B, adapted to NMT_tx1's distinct
nominal emitted constants with all steps freshly checked (L904/L906).
