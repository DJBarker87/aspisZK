# Joint functional binding cache provenance

`R1JointFunctionalBinding` was compiled successfully in the earlier focused
run preserved at
`../lean-joint-functional-binding-20261013/remote-evidence/`. Its source and
object are included here as imported dependencies, not rebuilt as part of the
Selected Opening Claims target.

The original successful attempt is `evidence/out-joint-functional-binding-r1-20261013h.log`
(run output SHA-256 `d2fd3dd83535880b4a37cee44694f7f05e75a4505defad3cb8adc425f15bf1ab`).
It names the compile source
`/home/dombarker/project-offloads/aspis-fs-generic-20261006/sources/R1JointFunctionalBinding.lean`,
which is pinned by
`evidence/sha-joint-functional-binding-r1-20261013h.txt` (sidecar SHA-256
`fa8ec67598f11cf6b49c960cd704eb8dcec7eef2034d1892f9a468bf1bac9115`) to source
SHA-256 `9a63100ea4e301a813c001beee84e5b4938748d8c429901f1668f6b54f344a19`.
The preserved source is `sources/R1JointFunctionalBinding.lean` (same hash).

The corresponding object is
`objects2/R1JointFunctionalBinding.olean`, SHA-256
`9845a9bf92815a6de7f98331f18cb0eca95586a85bb35d46fc6c801c02365c83`. The
paired timing record is `evidence/time-joint-functional-binding-r1-20261013h.log`
(SHA-256 `9ab726845e6be886943dac95e5d4906b53af36e4cc6d7c4a821731e57facff63`);
it records exit 0, 1.76 seconds, peak RSS 2,099,796 KiB, and zero swap. The
original deterministic evidence archive is
`lean-joint-functional-binding-20261013-evidence.tar.gz`, SHA-256
`33252bc6405d2da3a2643b0240034594852032a01a89ec5f23b38a6e80a915c7`. Its
`sources/R1JointFunctionalBinding.lean` member hashes to the source pin above,
and its `objects2/R1JointFunctionalBinding.olean` member hashes to the object
pin above. The successful run output reports the three public theorem axiom
sets as `[propext, Classical.choice, Quot.sound]`, with exit 0.

The Selected Opening Claims bundle repeats these same pins in
`source-manifest.json` and includes the files as
`import-sources/JointFunctionalBinding.lean` and
`objects/R1JointFunctionalBinding.olean`. That later target did not compile the
source in its own workspace; the original focused run above is the provenance
for the paired source/object hashes.
