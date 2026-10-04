# R804 complete fixed-witness active source row equalities

All214 active rows of the selected source matrix are now exactly equal to their saved sparse numerical rows at the fixed M31 parameter witness. This package adds213 row-function equalities in54 modules; row114 reuses its published prototype. Positive entries use the existing exact700-cell proofs; every other entry uses the compiled support-zero theorems. Five rejected plumbing attempts are retained. This establishes the active rows, not the full supplementary rows or determinant nonzero.

All 54 focused targets compiled successfully on pinned cached Lean4.32 with -j1 -M4500, separate5G/7G/no-swap/TasksMax128 scopes. The 213 complete axiom reports use only standard Lean axioms or subsets. Exact sources, logs, receipts, input pins, generation checks and available rejected attempts are saved. No successful compilation was repeated for publication.

| Target | source revision | source SHA256 | exit | wall | peak Lean RSS KiB | swap |
|---|---|---|---:|---:|---:|---:|
| `AspisV8R19/R804LiteralSourceRow1022.lean` | `ae67928cea0f528a6e221aff176d696be86823ea` | `bd5fde5d68e00ce991d73d77bb81e97f42c38e9d92cd971595e5a83f87b6d219` | 0 | 0:01.42 | 3316824 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk00.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `b3ba53ed21be9f5b3add41a7681e9d60727e1a6793b331f37df932dd19266944` | 0 | 0:01.99 | 3312200 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk01.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `64c44e2fde79dea3a56f34f553516b94aa15ed876257a498100f169a77f701f9` | 0 | 0:02.45 | 3322536 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk02.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `497279347ec3a4658ed58e10d9912b637839bf167ec205569ff270386221a71f` | 0 | 0:02.01 | 3316072 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk03.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `5d31d4753854fd4dce2e72c75940c2fcb54a6e42c97fb6084b0ebac015652bf8` | 0 | 0:02.11 | 3314988 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk04.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `688faaddedeabc7c8974525af62b619b6532e3412d0607ad1dab0563015c591e` | 0 | 0:02.31 | 3313040 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk05.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `ac24f160674459e3926601730a3dd96fe744a88e6f73704ee3baa41610d0639e` | 0 | 0:02.44 | 3320852 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk06.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `1fbc15418b32c1dc0568eba07e00c2bc087e089639e2452244e5ab37e0374546` | 0 | 0:02.15 | 3313280 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk07.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `95799185c296dd2c75abaa7c13d14818588b7b09389ba1002acad009c37c9deb` | 0 | 0:02.18 | 3319788 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk08.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `2f741787c6239c114565ba6445bc31b6537d108c4a8f44c9eabad1181a2a07cb` | 0 | 0:01.97 | 3318144 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk09.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `fa1a5df925a5ff769c32fc96954696e5f53104c1f5f2044058e2a34d872a57d8` | 0 | 0:02.09 | 3313128 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk10.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `f6514fd9baede39121b2c2e0b2ca5cace321faaf94454b4fb6e9b49ad7442cbe` | 0 | 0:02.24 | 3316504 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk11.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `0bdc5b8568ef694952093168bd6be169d2e06945ebf99715a47007f09cee6161` | 0 | 0:02.38 | 3320716 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk12.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `78c5615af2fef306f5a273a1d3732db3cbd7cb63a0edf19b65ed7598e04bfe3b` | 0 | 0:02.42 | 3316468 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk13.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `4bee1f61c12e8a8ffc159a591e008e30dd8c57834ca66b403e1082a3c33a3646` | 0 | 0:02.26 | 3321328 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk14.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `fd71f9ad2953f4bd31ea662132be350dff2627945f47d70c4558e96649635176` | 0 | 0:02.31 | 3314268 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk15.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `6b8c2341345527134017dd30e42b0f95f6acc897698ee1cc9d71de22f4731854` | 0 | 0:02.17 | 3316320 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk16.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `08585a827b387d9b815f26fb99e2b6b0bbf7f45aedff270bf84c7c9a690cab8c` | 0 | 0:02.45 | 3319684 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk17.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `34a3f6a571579c98de2a30b5b205c43d15e003daa8fdb228a19f00eec77e33cc` | 0 | 0:02.08 | 3314792 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk18.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `f3d2b8cab831168269574e8d6ed69ca3482f7890373238cd55f01c6306de4486` | 0 | 0:02.17 | 3316660 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk19.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `0eb2271d65124f25fcd0c7099cfda4e3bd762474cbb42036ec54847614a658d9` | 0 | 0:02.08 | 3315160 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk20.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `587608b246d4ecf4a7b3f1602be8c8c981559ab4cd0976bf91288bddd138fa0d` | 0 | 0:02.35 | 3315016 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk21.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `1a2c448d2bf5c7c862d0d40548990a31fd1ffd07d6ef655b52f7cc0d7adea8f6` | 0 | 0:02.16 | 3314548 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk22.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `786e57941c6efb373a98b382221964cbb4cb271478f6d870dfc2ce62b8b1e932` | 0 | 0:02.20 | 3311548 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk23.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `0f66cddcc599df5f73400d1c919ff0bd42e14450677ec127e93d35af70df63ea` | 0 | 0:02.15 | 3316648 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk24.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `c9a3eeee435f3751ec84ee0ed795dfa89096a394d7810fedb6125ac6538c21ee` | 0 | 0:02.30 | 3314796 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk25.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `e34f9eab385ce68e05be70998e2aaecb2baf991c46277bae397bc0ddca6354fa` | 0 | 0:02.14 | 3316088 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk26.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `a06d2d60bc4ba90b539c28935693c460984ecbdfa2bac5523699a56d3c87e461` | 0 | 0:02.22 | 3314072 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk27.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `6953dab5430504262c47f4bdf308f39ff0ab814a466b00c857a411be137fafa2` | 0 | 0:02.24 | 3314544 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk28.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `83113a93fdfb228aa0edb0ccbc48e88078787d68966b3ec89d2e1201e44ed173` | 0 | 0:02.22 | 3315260 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk29.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `33d48aa8fc2994a39480630c7088fe4eb40f1d1f8a32830cfa8d44e9d080d591` | 0 | 0:02.01 | 3319124 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk30.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `c2f40cc0ea0e8c67d7c2fa91cec34608455a524bd31f1988b0e15d388304b7f8` | 0 | 0:02.45 | 3316776 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk31.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `a54e4a73634826708d5b0961dc90e82dd03f0608c895ee43fd7d7a8f0b54c2b5` | 0 | 0:02.22 | 3320288 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk32.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `59e87271eb19fd3ed1880639f40ecb55f808d43e668390f22f438542af0ee127` | 0 | 0:02.21 | 3321280 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk33.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `d5da0314ccb708849c650bd138c8ac91f80fc86c8d61e861d7c8fe875eb1a11a` | 0 | 0:02.05 | 3317056 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk34.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `243529e51120d1c7b897cccc7a63067cba8a1bbbe6e10302d0c7ffce5f7ae5f3` | 0 | 0:02.92 | 3323348 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk35.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `a33d4d2063e98e640e99fc17153d9991e421a9e18f7cdd070327d811935b7446` | 0 | 0:02.32 | 3317764 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk36.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `2ec0101b076badd7d6b77a4f489756817976343b58217ab66579c00eaac53931` | 0 | 0:02.33 | 3321364 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk37.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `e81c38d3af2819d6d06c43a43e6363fbb9200086711070045060e8994213944f` | 0 | 0:02.52 | 3333320 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk38.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `69db8ecec9258c9466b908b1a88a7bb86162348f8a3c853cc61f831019bb78c2` | 0 | 0:02.36 | 3320996 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk39.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `3eaa890792dbc87f857aec82f8c100eae4e8e3f4dd8f4cb4644a310471890849` | 0 | 0:02.91 | 3326128 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk40.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `59dcdb8ec27d22809f05fdbd1128d705336d2212673a543f6c6c8a7339b4be75` | 0 | 0:03.03 | 3326972 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk41.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `1cc79b304f4a6b55708ae301b60ec7f367e9bcb52817f803ad371208e089aae2` | 0 | 0:02.98 | 3329724 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk42.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `43ef149a802bdbf4de84c1e73e7003ce2a45984769ea9ebf5b6dd127c48eb3a9` | 0 | 0:03.11 | 3332004 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk43.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `6d3c796b718b25c1bf8568b5370f76814a2960fa07bc1e621a99bc1eddc51653` | 0 | 0:03.08 | 3327484 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk44.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `752cc44884a6ae423d02c825af429f077de7e8a369c47539b99a5ed7cbbb74d7` | 0 | 0:02.76 | 3327040 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk45.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `224e7142253b8fbe2c0185bb147c0e3e102a97fffd53d5f7b67ccf5dadb1d19c` | 0 | 0:02.93 | 3332500 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk46.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `b37b370f4922cfeca12e028831f68a4ac1a181e5806f1be895a94031fd7d2ddc` | 0 | 0:02.86 | 3321116 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk47.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `c36b51906bae06ed2fc8a013ebd1a7bbc56c1724a861375f5dd2c68006faf6d9` | 0 | 0:03.08 | 3327564 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk48.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `4adb6b9e62fe1093698011f7e10cfb5ef82107ea0c4c803550b42008441b7972` | 0 | 0:02.89 | 3321452 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk49.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `2b1d8ca3a56855655149e50470c76cd73a95720758b845d4185c1f67786cc4b0` | 0 | 0:03.10 | 3332776 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk50.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `02b9c5933f0511e3ea64690312bd3027e32ce022cadaf9ece84a055f1c630980` | 0 | 0:03.17 | 3323352 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk51.lean` | `0bcddf6226ee78d1c1da1adb3cf92ce7e7cae2b3` | `fb9facd336dc1357abf5988a947e59640463a28c32160734bf9b8b87b341b6f9` | 0 | 0:02.63 | 3322412 | 0 |
| `AspisV8R19/R804LiteralSourceRowsChunk52.lean` | `ae67928cea0f528a6e221aff176d696be86823ea` | `a2e20c0accc56ac0c4cabf640cb2fdc5344b367001c444588ec9791820e78407` | 0 | 0:02.53 | 3325208 | 0 |

First remaining proposition: Bind all41 source diagonal blocks and prove source block triangularity; supplementary point/coefficient entries and the unconditional source determinant remain to be closed.

Verifier results999,790/999,532CU and all security parameters unchanged. Full privacy, native execution, published-view simulation, probability bounds and soundness remain unproved.
