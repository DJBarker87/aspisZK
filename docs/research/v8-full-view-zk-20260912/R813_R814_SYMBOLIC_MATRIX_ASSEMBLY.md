# R813/R814 symbolic finite function and block-row assembly

Generic function extensionality for Fin dimensions1,2,3,4,6,8,16,39 is compiled with abstract function arguments and explicit scalar equality premises. It permits consumers to use already-proved row/cell equalities without expanding finite cases over full source expressions. The R814 generic block00 row reindex theorem separately proves the exact six selected column indices for any222x222 matrix, before source instantiation. These are exact symbolic assembly facts, not concrete source block equality, determinant nonzero or security. One rejected generic import attempt is preserved.

All 9 focused targets compiled successfully on pinned cached Lean4.32 with -j1 -M4500, separate5G/7G/no-swap/TasksMax128 scopes. The 10 complete axiom reports use only standard Lean axioms or subsets. Exact sources, logs, receipts, input pins, generation checks and available rejected attempts are saved. No successful compilation was repeated for publication.

| Target | source revision | source SHA256 | exit | wall | peak Lean RSS KiB | swap |
|---|---|---|---:|---:|---:|---:|
| `AspisV8R19/R813FinSixExt.lean` | `2a754e6b1bbd272535c0c9a03d83285d1be3ba18` | `3d81b36282cda87116ac7ded6b53c94b7bf8d6c5a4edb129fe17162c581b709e` | 0 | 0:00.68 | 1535908 | 0 |
| `AspisV8R19/R813FiniteFunctionExt1.lean` | `50e2886e1db6913cf4efb00d12fa60a8aefcf351` | `afcc9626519cd739d81a4a5fa80b686e701a01e179b20f911c57c28081ded4a8` | 0 | 0:00.63 | 1532772 | 0 |
| `AspisV8R19/R813FiniteFunctionExt2.lean` | `50e2886e1db6913cf4efb00d12fa60a8aefcf351` | `a7f6637e68fd8bfdfd4c47992fa33683c213641439465bc9a6387f4a0aafd18f` | 0 | 0:00.62 | 1532900 | 0 |
| `AspisV8R19/R813FiniteFunctionExt3.lean` | `50e2886e1db6913cf4efb00d12fa60a8aefcf351` | `c75fada85edac807e380893053e11117d96fc8d14f9d67d056b02dc0bcf80c9f` | 0 | 0:00.62 | 1534368 | 0 |
| `AspisV8R19/R813FiniteFunctionExt4.lean` | `50e2886e1db6913cf4efb00d12fa60a8aefcf351` | `db111b884e6c4eaa3b82fee2fc796d24b3ceaed6ae66b21bf343c59d2f8e3bd2` | 0 | 0:00.62 | 1532940 | 0 |
| `AspisV8R19/R813FiniteFunctionExt8.lean` | `50e2886e1db6913cf4efb00d12fa60a8aefcf351` | `d0e036a39af9111c99d95226527c2c87af7dd6e96605527a7c9821b26d8c31ce` | 0 | 0:00.69 | 1536080 | 0 |
| `AspisV8R19/R813FiniteFunctionExt16.lean` | `50e2886e1db6913cf4efb00d12fa60a8aefcf351` | `e58351b0032d57bb8ed17c8d746b06644ece031c94fc7059727a9912373a3794` | 0 | 0:00.81 | 1540468 | 0 |
| `AspisV8R19/R813FiniteFunctionExt39.lean` | `50e2886e1db6913cf4efb00d12fa60a8aefcf351` | `c16a827e33e1a6967f6e186699db479b3f550f0464d5da924fc70dfe9f182db5` | 0 | 0:00.83 | 1555372 | 0 |
| `AspisV8R19/R814BlockZeroReindex.lean` | `50e2886e1db6913cf4efb00d12fa60a8aefcf351` | `235ac96e6915934ee4520ff2cf561fae614187090e7c8546260cbd2a9a831268` | 0 | 0:01.42 | 3320852 | 0 |

First remaining proposition: Consume these symbolic extensionality/index facts to assemble the source diagonal block equalities within the existing memory cap; actual block-triangularity and all diagonal source bindings must still be discharged.

Verifier results999,790/999,532CU and all security parameters unchanged. Full privacy, native execution, published-view simulation, probability bounds and soundness remain unproved.
