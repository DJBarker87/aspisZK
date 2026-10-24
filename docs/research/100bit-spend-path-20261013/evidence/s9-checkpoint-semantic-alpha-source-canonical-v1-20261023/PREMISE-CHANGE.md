# Exact statement and remaining scope

The new final theorem is `AspisR1S9ResumeSemanticAlphaCanonicalV1.successful_resume_semantic_alpha_canonical`. It quantifies over arbitrary base ResumeOps, a Digest32 instance, checkpoint/proof/public byte slices, variant, hash, returned Prepared p and Accumulator acc, and a successful array read of p.semantic_alpha.

Its run premise is success of `resumeWithOps (withSemanticAlpha ops)` returning those same p and acc. Its index premise is `Array.index_usize p.semantic_alpha i = .ok q`. Its conclusion is the four explicit limb bounds q.c0.a, q.c0.b, q.c1.a, q.c1.b below2147483647. There is no assumed successful helper/decoder call and no canonical input/output premise. The same-resume Fields witness is derived internally from that run.

The generic reader model lemma has a callback-preservation hypothesis; the concrete semantic-alpha theorem discharges it with `readerK_success_canonical`, so it is not retained as a free final premise. The intermediate source-equality theorem is unconditional over every read operation: it rewrites the generated Rust Result try/FromResidual blocks into ordinary Err/Ok matches, preserving all outer failure/divergence and short circuits.

Previously the constructor theorem required canonical input alpha. This packet supplies that exact shape on actual p.semantic_alpha reads in the installed resume content model, so a structural carrier-copy/caller join can discharge that constructor premise. The packet does not itself perform that later constructor join or prove actual native caller installation.

ReaderK uses the retained full16-byte decoder and a fieldwise output carrier adapter. Raw Reader behavior, its concrete old-to-current decoder/source correspondence and current Rust callback/runtime adoption remain explicit source-refinement tasks. These are implementation obligations, not cryptographic assumptions. The compact proof-buffer grammar is distinct and not changed or reproved here.
