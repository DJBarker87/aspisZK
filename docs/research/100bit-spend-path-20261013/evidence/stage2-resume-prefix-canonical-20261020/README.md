# Stage2 resume prefix canonical outputs (2026-10-20)

This focused Lean result composes the source-ordered fixed-read prefix with concrete retained QM31 and WideExact decoder canonicality. If the prefix returns successfully with the concrete decoders, gamma, kappa, alpha0, alpha1, and rho are canonical. The `unwrapArray` adapter remains arbitrary; no byte identity or parser unwrap correctness is claimed.

The prefix theorem is a source-cut adapter through the `rho = r.k()?` read after c8 authentication checks. This is not a theorem about the whole `stage2_resume` function. Query reads, later mutable loops, checkpoint hashing, and authentication are outside this result.

The consumer's direct imports are pinned in `config.json` and `attempt/preflight.json`: `Stage2ResumeFixedReadPrefix` object SHA `90f521b402b43deab50d3cd6123c0779e08e33276a740fcc1355270c80ada485`, and `Stage2ResumeConcreteDecoderCanonicality` object SHA `da5f7f4bee6e4c769516bc7279d86982724b61960447036e1759113c451d32c9`. The fixed-prefix source packet is `../stage2-resume-fixed-prefix-20261019`; the concrete decoder source SHA is `850f08a2ec18e7b96bdbc3c90bb74890ba416ba48fc909348b56f6af0fc295ab`.

Validation: NUC Lean 4.32 focused proof, exit 0, wall 1.304s, peak process RSS 2,637,788 KiB, cgroup peak 291,258,368 bytes, swap peak 0. `lean.log` reports axioms `[propext, Classical.choice, Quot.sound]`. No OLean is included in this source/evidence packet; the object SHA is recorded in `attempt/receipt.json`.

The decoder dependency source and its own exact validation evidence are included under `sources/Stage2ResumeConcreteDecoderCanonicality.lean` and `dependency-attempt/`. Its source SHA is `850f08a2ec18e7b96bdbc3c90bb74890ba416ba48fc909348b56f6af0fc295ab`, object SHA `da5f7f4bee6e4c769516bc7279d86982724b61960447036e1759113c451d32c9`, exit 0, wall 1.304s, process RSS 2,641,424 KiB, cgroup peak 293,294,080 bytes, swap 0. It reports only `[propext, Classical.choice, Quot.sound]`.

The current prefix is a hand-isolated Lean read sequence. Its equality with a Charon/Aeneas-extracted prefix cut is still OPEN, as is reaching that prefix from successful whole-resume execution. The manifest labels this source correspondence as CANDIDATE.
