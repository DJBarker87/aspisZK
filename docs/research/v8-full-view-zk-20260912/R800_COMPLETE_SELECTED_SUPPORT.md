# R800 complete selected active support and source zeros

All214 active rows now have exact support masks over the222 selected columns and generic CommRing proofs that sourceChord is zero outside its support. This package adds212 rows in53 modules; rows114 and1022 reuse the published prototype. Combined with the700 positive cell proofs, these facts permit complete fixed-witness active row assembly. These support theorems do not by themselves prove matrix rank.

All 53 focused targets compiled successfully on pinned cached Lean4.32 with -j1 -M4500, separate5G/7G/no-swap/TasksMax128 scopes. The 424 complete axiom reports use only standard Lean axioms or subsets. Exact sources, logs, receipts, input pins, generation checks and available rejected attempts are saved. No successful compilation was repeated for publication.

| Target | source revision | source SHA256 | exit | wall | peak Lean RSS KiB | swap |
|---|---|---|---:|---:|---:|---:|
| `AspisV8R19/R800SelectedSupportChunk00.lean` | `d2f3e839773403c24e13c202d7e9ab08613ce2ba` | `35a74176ee9b981606d3b544199b0c7c3d12661ec2a1123faba6a2b7e59c6ffc` | 0 | 0:16.40 | 3791888 | 0 |
| `AspisV8R19/R800SelectedSupportChunk01.lean` | `d2f3e839773403c24e13c202d7e9ab08613ce2ba` | `7cb333b090e76202c567ddffda788a85a6ad65950908569d5742feabdca70411` | 0 | 0:16.88 | 3810364 | 0 |
| `AspisV8R19/R800SelectedSupportChunk02.lean` | `b9a129d7af99d4d770f32b12ffd42b213e86ee33` | `35cfc6d134e288dcde562b64276ba26c2e69e985607f1e01f1102adcd98e11af` | 0 | 0:16.04 | 3790716 | 0 |
| `AspisV8R19/R800SelectedSupportChunk03.lean` | `b9a129d7af99d4d770f32b12ffd42b213e86ee33` | `fad7d0306d1e0bf7e2ebd09c31cecae7d4f73076f65cc26527a932a271846104` | 0 | 0:16.56 | 3795920 | 0 |
| `AspisV8R19/R800SelectedSupportChunk04.lean` | `b9a129d7af99d4d770f32b12ffd42b213e86ee33` | `249eb614d7e2045dd92555e8f10359c11f3f8580ce7d1d861793363bd1494e34` | 0 | 0:16.89 | 3792460 | 0 |
| `AspisV8R19/R800SelectedSupportChunk05.lean` | `b9a129d7af99d4d770f32b12ffd42b213e86ee33` | `0c99bb01c4dad3e5d3eae1da600a508ce4d349eae57002b906a75b33562f76cf` | 0 | 0:16.74 | 3801944 | 0 |
| `AspisV8R19/R800SelectedSupportChunk06.lean` | `b9a129d7af99d4d770f32b12ffd42b213e86ee33` | `534f1c7be2f06848f43249896aec6f0675191e5286179f4005e882e0643b524c` | 0 | 0:16.40 | 3792800 | 0 |
| `AspisV8R19/R800SelectedSupportChunk07.lean` | `b9a129d7af99d4d770f32b12ffd42b213e86ee33` | `34bdb846eb7acbd114bbf20b198e67c154d524207fae306e0378ece185b29fb9` | 0 | 0:16.71 | 3741992 | 0 |
| `AspisV8R19/R800SelectedSupportChunk08.lean` | `b9a129d7af99d4d770f32b12ffd42b213e86ee33` | `bfe850955e38649f66c4800d99637b11c1c4685cdff983ec104ecf3fb5c0835b` | 0 | 0:18.34 | 3785928 | 0 |
| `AspisV8R19/R800SelectedSupportChunk09.lean` | `b9a129d7af99d4d770f32b12ffd42b213e86ee33` | `5c96e51ef2ca8aac34306efbb151787a75bfbd10e5f28e35534daaf1b17aa552` | 0 | 0:16.97 | 3792052 | 0 |
| `AspisV8R19/R800SelectedSupportChunk10.lean` | `b9a129d7af99d4d770f32b12ffd42b213e86ee33` | `816b62a9f3666cf535d62f2376a462f5bb4272082d3cc495da53469760dbbb7a` | 0 | 0:18.31 | 3796660 | 0 |
| `AspisV8R19/R800SelectedSupportChunk11.lean` | `3531131df0f1db920c5ee48e9e386e53bdba18e9` | `aff58de993f6916bf97ac179ac21b944ab9ed6c6953923fba2c94932b72b7a42` | 0 | 0:17.20 | 3792212 | 0 |
| `AspisV8R19/R800SelectedSupportChunk12.lean` | `3531131df0f1db920c5ee48e9e386e53bdba18e9` | `66ef1c1133a752c270baa244a00a0c31243978d71d09ef55ca390270fa7509d2` | 0 | 0:18.02 | 3801000 | 0 |
| `AspisV8R19/R800SelectedSupportChunk13.lean` | `3531131df0f1db920c5ee48e9e386e53bdba18e9` | `cb4956ad7a9940dd8edda45ff17ae6003db6b10eea6aa79f504eab45817947de` | 0 | 0:17.24 | 3791628 | 0 |
| `AspisV8R19/R800SelectedSupportChunk14.lean` | `3531131df0f1db920c5ee48e9e386e53bdba18e9` | `2a9fc98c99e0f39234323dce55a8b65889303466c15d3d1a150628af2724cb97` | 0 | 0:16.34 | 3795584 | 0 |
| `AspisV8R19/R800SelectedSupportChunk15.lean` | `3531131df0f1db920c5ee48e9e386e53bdba18e9` | `32dd2ef00aa7d1662f9cae51c43f5eb34b70692ee3af07b05562fc3ecad993da` | 0 | 0:14.24 | 3740732 | 0 |
| `AspisV8R19/R800SelectedSupportChunk16.lean` | `3531131df0f1db920c5ee48e9e386e53bdba18e9` | `f12377bc736314ce91ab87bfff6e0313d569a988d9a3daca30d9115555d04f93` | 0 | 0:14.02 | 3743740 | 0 |
| `AspisV8R19/R800SelectedSupportChunk17.lean` | `3531131df0f1db920c5ee48e9e386e53bdba18e9` | `736be2f727fc65c3c05e18621bc986a7465ebf5f800fe5b0cf4edcba34127ab2` | 0 | 0:13.07 | 3744200 | 0 |
| `AspisV8R19/R800SelectedSupportChunk18.lean` | `3531131df0f1db920c5ee48e9e386e53bdba18e9` | `4e880d49bfed96e8bfa218d88d57c0be069e4f66392876ab5f4d3dc424a71f4b` | 0 | 0:13.07 | 3743068 | 0 |
| `AspisV8R19/R800SelectedSupportChunk19.lean` | `3531131df0f1db920c5ee48e9e386e53bdba18e9` | `537bbdfe67ad99326c2aaca0f5524e9cd44a14419d228de4f5caf4dc14698e48` | 0 | 0:12.71 | 3745912 | 0 |
| `AspisV8R19/R800SelectedSupportChunk20.lean` | `3531131df0f1db920c5ee48e9e386e53bdba18e9` | `ee18f4e8e8b9104324636db2617652d20e9eceab99167b1418f9014b7a19627b` | 0 | 0:13.69 | 3744216 | 0 |
| `AspisV8R19/R800SelectedSupportChunk21.lean` | `3531131df0f1db920c5ee48e9e386e53bdba18e9` | `80544f621fbcb6219ddd6c324b40d5ee8d4c535088e4ebde7f9f5d899bdba153` | 0 | 0:12.70 | 3742840 | 0 |
| `AspisV8R19/R800SelectedSupportChunk22.lean` | `3531131df0f1db920c5ee48e9e386e53bdba18e9` | `b8e51a97ab1b95133743470bc7fb99f9621286815b4283faa121b2812f86a90d` | 0 | 0:12.92 | 3738672 | 0 |
| `AspisV8R19/R800SelectedSupportChunk23.lean` | `7a072106ad6b7f659a8d697b32f864deefc4f3a5` | `0a4f0ea6999a7f145fde11b4144c0a577529904a6f958e9f225238793e1638d4` | 0 | 0:12.50 | 3740644 | 0 |
| `AspisV8R19/R800SelectedSupportChunk24.lean` | `7a072106ad6b7f659a8d697b32f864deefc4f3a5` | `2199dc417e7ea67079e960c54178d2d0ce7fa2931cea1657fef804c8cb99e2f9` | 0 | 0:12.33 | 3740608 | 0 |
| `AspisV8R19/R800SelectedSupportChunk25.lean` | `7a072106ad6b7f659a8d697b32f864deefc4f3a5` | `49885452e73feafb2df9596baf56bae36453fe956e1e6c64c5a77961b2a7709e` | 0 | 0:12.38 | 3739956 | 0 |
| `AspisV8R19/R800SelectedSupportChunk26.lean` | `7a072106ad6b7f659a8d697b32f864deefc4f3a5` | `e51084fdb4e4a65702fe1ae2d24505cf534039b03a2746341ba61e924151c5af` | 0 | 0:12.67 | 3741348 | 0 |
| `AspisV8R19/R800SelectedSupportChunk27.lean` | `7a072106ad6b7f659a8d697b32f864deefc4f3a5` | `9544d20c270d961080b3f684cee33b137d1a5962a22218cd4fc23d3162318053` | 0 | 0:12.72 | 3740784 | 0 |
| `AspisV8R19/R800SelectedSupportChunk28.lean` | `dc2b3469f760ff1279ec3ae6bb897aa63d095ab4` | `b4988d5cc6f7c21f4a5d67c60bc25411fd4901e280c32351f6775735e45dd511` | 0 | 0:12.72 | 3740912 | 0 |
| `AspisV8R19/R800SelectedSupportChunk29.lean` | `dc2b3469f760ff1279ec3ae6bb897aa63d095ab4` | `22783498418ec086fca8d931f431528d6165ab9d979503c0d54a0cf806434ad5` | 0 | 0:13.58 | 3689172 | 0 |
| `AspisV8R19/R800SelectedSupportChunk30.lean` | `dc2b3469f760ff1279ec3ae6bb897aa63d095ab4` | `40b12a865d96ef58df4de20f7f774105d919990b3bf4888f327891061352f121` | 0 | 0:15.01 | 3692112 | 0 |
| `AspisV8R19/R800SelectedSupportChunk31.lean` | `dc2b3469f760ff1279ec3ae6bb897aa63d095ab4` | `e6ad6e55dcf2249490d2201e44da1164c35a2e4e6b7990e2db6a199f939f13e8` | 0 | 0:14.87 | 3677444 | 0 |
| `AspisV8R19/R800SelectedSupportChunk32.lean` | `dc2b3469f760ff1279ec3ae6bb897aa63d095ab4` | `ab7e75ddce0c466b84a9537fb4211212475314c7fefa9f9fe60d6bfa5d86450f` | 0 | 0:13.21 | 3650180 | 0 |
| `AspisV8R19/R800SelectedSupportChunk33.lean` | `dc2b3469f760ff1279ec3ae6bb897aa63d095ab4` | `09ad5b80473968ab8ba15a1a3a9229e6e5a0a01253054a162c65ce62d0d053eb` | 0 | 0:15.18 | 3784976 | 0 |
| `AspisV8R19/R800SelectedSupportChunk34.lean` | `dc2b3469f760ff1279ec3ae6bb897aa63d095ab4` | `17be5e55eb8e317d1633234ffda7cbda66ca8d089f1614797beda23797a13bfd` | 0 | 0:16.47 | 3790248 | 0 |
| `AspisV8R19/R800SelectedSupportChunk35.lean` | `dc2b3469f760ff1279ec3ae6bb897aa63d095ab4` | `b9cc5dc5ce68ab39f4521a542f9c7cad81c6e5273e0019af6774409483b0b4b2` | 0 | 0:14.53 | 3639668 | 0 |
| `AspisV8R19/R800SelectedSupportChunk36.lean` | `dc2b3469f760ff1279ec3ae6bb897aa63d095ab4` | `55d64de9a5a28248dc35caa858e01afee2430fc112a3b02d4b6859861892cc6e` | 0 | 0:14.62 | 3691096 | 0 |
| `AspisV8R19/R800SelectedSupportChunk37.lean` | `dc2b3469f760ff1279ec3ae6bb897aa63d095ab4` | `1e0d42c9ab18c16230fc4f98bb6bce3a647c7214bf42ebb890879cf08ddab259` | 0 | 0:16.44 | 3772184 | 0 |
| `AspisV8R19/R800SelectedSupportChunk38.lean` | `dc2b3469f760ff1279ec3ae6bb897aa63d095ab4` | `fc910dd237b91d9b4605288ec6de084e7d9a08c529478fcf5b7630c37a599047` | 0 | 0:17.56 | 3761548 | 0 |
| `AspisV8R19/R800SelectedSupportChunk39.lean` | `dc2b3469f760ff1279ec3ae6bb897aa63d095ab4` | `9ed2548bd0d99ada9c91ca295ed1249d35d53df3745ef0726a35e81ba8b88247` | 0 | 0:17.55 | 3789232 | 0 |
| `AspisV8R19/R800SelectedSupportChunk40.lean` | `dc2b3469f760ff1279ec3ae6bb897aa63d095ab4` | `631078d684de12f321766c86f50cdc67574b5a8c878508e19d3b0fb0f25daf22` | 0 | 0:16.94 | 3800276 | 0 |
| `AspisV8R19/R800SelectedSupportChunk41.lean` | `dc2b3469f760ff1279ec3ae6bb897aa63d095ab4` | `1b54227da8cde28f70485d9735af3ce6fdcf45c0d12d0713e038a62bfc10a08c` | 0 | 0:18.81 | 3794960 | 0 |
| `AspisV8R19/R800SelectedSupportChunk42.lean` | `dc2b3469f760ff1279ec3ae6bb897aa63d095ab4` | `d26ad10fe867000a8a42a1452206a3ab021397ee31c5f9de56c8b1b919ddbe86` | 0 | 0:17.02 | 3801564 | 0 |
| `AspisV8R19/R800SelectedSupportChunk43.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `49993f96e28976fb04b05ddb3025c58f36cc124e8072eca371396096b4124f52` | 0 | 0:18.71 | 3795408 | 0 |
| `AspisV8R19/R800SelectedSupportChunk44.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `ff6cd80b1af557822795d035ed16245be6735c79768b363dca9395ab4b9e4c72` | 0 | 0:17.02 | 3793184 | 0 |
| `AspisV8R19/R800SelectedSupportChunk45.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `47c731c7572cacae2e42bae09aa6a130bcf16bfd7ae59ddee00879cf370cb322` | 0 | 0:17.05 | 3800012 | 0 |
| `AspisV8R19/R800SelectedSupportChunk46.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `5a78de949c6cea7e73bf14d947910c597a010c4c6b69d990523d37952ad4b5bf` | 0 | 0:17.03 | 3789288 | 0 |
| `AspisV8R19/R800SelectedSupportChunk47.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `7bfb42d393f4707bdc4f568394adfcb947880fc47128208ab6a766376243d906` | 0 | 0:16.92 | 3702424 | 0 |
| `AspisV8R19/R800SelectedSupportChunk48.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `aa4fad162a4d8f2c3d4e23222a4fca4c7e43cfa944a6d517fe7f57bcf8dd6a41` | 0 | 0:18.35 | 3698116 | 0 |
| `AspisV8R19/R800SelectedSupportChunk49.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `63795a6110ba9d52c6a155a4381cd9279f64bd9cc6c5e14bcb94a6b46085f9e7` | 0 | 0:17.64 | 3736532 | 0 |
| `AspisV8R19/R800SelectedSupportChunk50.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `6900c66cc8284c6dcbc8bb000049cd5904361d7fb123a7366e1b849e3b018f97` | 0 | 0:17.77 | 3728240 | 0 |
| `AspisV8R19/R800SelectedSupportChunk51.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `ab4e42f7735696c9bac1fb3a761ce924022ea24e96db272dbeb5340187d84cb0` | 0 | 0:17.79 | 3781388 | 0 |
| `AspisV8R19/R800SelectedSupportChunk52.lean` | `f783df95855e64e0f33a9f9c39d67016730ab94c` | `7d5775184794e8aeedeb555c0c0436ce1f677a8e6272393277e9d918dc74dd0e` | 0 | 0:14.70 | 3745716 | 0 |

First remaining proposition: Assemble every fixed-witness source row, bind all diagonal source blocks to the existing inverse certificates, prove source block triangularity, and derive unconditional source determinant nonzero.

Verifier results999,790/999,532CU and all security parameters unchanged. Full privacy, native execution, published-view simulation, probability bounds and soundness remain unproved.
