# Focused Lean target resource and axiom record

Axiom-report counts are the number of `depends on axioms` lines in the captured log. A zero for generated Types/Funs means there were no `#print axioms` commands in those files. Process-swap status is taken from each captured `/usr/bin/time -l` log.

| Attempt / target | Exit | Wall s | Sampled aggregate RSS KiB | Axiom reports | Axioms seen | Process swaps zero | Source SHA-256 | Object SHA-256 |
|---|---:|---:|---:|---:|---|---|---|---|
| `types-a` / `AspisR1Qm31ArithmeticProbe.Types` | 0 | 16.381 | 2765664 | 0 | none printed | yes | `c5a08408bb25ca84fcef1b3689904d27e65510c21775d6db8beeb271fbaa5b15` | `dc0d87773f83da6e59760621756fea3c6184de6da70d9c2987b750982e9cd574` |
| `funs-a` / `AspisR1Qm31ArithmeticProbe.Funs` | 0 | 5.086 | 2797424 | 0 | none printed | yes | `114552b863f61e970a2ceb4bb048566e4b464b61905c6d7a175f6b117f1aed4a` | `d0e7b67a90096dd96cd3c71a16d804fda4073b07f215fd14e3db23ea148be1ae` |
| `m31-add-sub-a` / `ExtractedCurrentM31AddSub` | 0 | 15.926 | 2772848 | 2 | propext,Classical.choice,Quot.sound | yes | `84100aa24d1e1431798195ff0d5d548ac6e03cd3c0149c5a3251833f30bec568` | `6e404a500b2800de7e45e740cb5754f191275d02b2701ef356e871372bfa58ac` |
| `retained-reducer-nat-a` / `AspisV8R17.RawReducerNat` | 0 | 2.535 | 1059008 | 4 | propext,Classical.choice,Quot.sound | yes | `1c65a462b3309e339750f518a1a37931b4c0595aa47cd04a830747b0d41f0101` | `a15c5d070f7862dac4b5bac98e7e525cb23c8b816d6663aa746bd993b4c1c051` |
| `reducer-ops-a` / `ExtractedCurrentReducerOps` | 0 | 12.164 | 2712304 | 8 | propext,Quot.sound | yes | `393671317c3199ed4d62f1b6ec65e848ec9c831d0dfad740ea0f5ceed47595a5` | `6ade82f8d9864ed57762754a24631b8904d802acbac6d1b034a18c235f4efecf` |
| `current-reducer-a` / `ExtractedCurrentReducer` | 0 | 9.408 | 2717504 | 9 | propext,Classical.choice,Quot.sound | yes | `933ae275dac978bd0ac60035154e5274c4f1a12bffcbc98f2265fbd50e49af74` | `0e349fbb354fcf7b6d6d581f2d3f830b91f352d640624b756fd53398254eed7b` |
| `tower-add-a` / `ExtractedCurrentTowerAdd` | 0 | 10.967 | 2712864 | 3 | propext,Classical.choice,Quot.sound | yes | `99af475da13f6066d8aefbbf19c062858648abea980a94e98bc1ed14488e5166` | `1c1bb85001123d34327c00a7d8769d5ea114d30ff26a584789ff48dc4d1d4d6e` |
| `cm31-mul-a` / `ExtractedCurrentCM31Mul` | 1 | 13.596 | 2775456 | 6 | propext,Classical.choice,Quot.sound,sorryAx | yes | `4810a007c3b8399f3e64e372a391c0bc70f1b9d639e7c64350d57a8dbe9bfef7` | `none` |
| `cm31-mul-b` / `ExtractedCurrentCM31Mul` | 0 | 15.332 | 2793712 | 6 | propext,Classical.choice,Quot.sound | yes | `0364f578089cdf613c406f527d59096673c84242f5cabfc2c13c6ed05075ab1d` | `084409df29e99b44c44c05cde8ea9b015e6f0a4406555898c628b13835569fcb` |
| `qm31-mul-a` / `ExtractedCurrentQM31Mul` | 1 | 8.691 | 2774864 | 1 | propext,Classical.choice,Quot.sound,sorryAx | yes | `b071a9b498524f6ba800aafedbe1a86e5885ab0835bf99f58a55e13217282a54` | `none` |
| `qm31-mul-b` / `ExtractedCurrentQM31Mul` | 0 | 5.156 | 2760208 | 1 | propext,Classical.choice,Quot.sound | yes | `954b173f71eaf1c59da6ff32e9fbe10a9047fbcca622b85a85a01588b0134d66` | `06038a3ebd4f8c4a44f7be169e1345f683f8340561774c494d2a355ac2094416` |

`cm31-mul-a` failed at the intermediate `(2^32)*(2^32)` bound. Its compile log has an error and `sorryAx` diagnostics; it is not a theorem result. `cm31-mul-b` is green with six standard-only axiom reports and the explicit product-overflow bound, no premise change. `qm31-mul-a` failed at an unsolved goal, no object, and its log includes `sorryAx`; `qm31-mul-b` is green with one standard-only axiom report. Both failed attempts are preserved.
