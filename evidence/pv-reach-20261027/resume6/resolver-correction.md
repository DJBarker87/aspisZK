# Joint/union authority correction

The initial resolver used a last-entry-wins dictionary over EJR_final-inventory.selected. That file has duplicate module names under the joint and union workspaces. For env-J, the joint row takes priority. The initial counts and complete inventory are retained as project-closure-initial-union-overwrite.json and are superseded as a claim about the canonical joint closure.

The two apparent PublicPreparation conflicts in pinned-cache-links.json were caused by that resolver error: the host source hashes equal the joint records, not the union records. No mismatching link was installed and no shared source was written.

The corrected resolver holds the installed dictionary closure at R1Z.BuilderAdmissionExtracted. Its joint resolved blob is 88551b1778e2a1541ab7092ac8c02d326cfadce0 (SHA bbddadb0e25cf688dcc625ff0a623fdb83b1a80fe3e9d4d798025123f74e12ef); the HEAD-tracked source has blob 93b916f44ca47b2a37353590bf9345a5ca378ed7 (SHA 19d637faebb2eb5aa0d8e2f66e0e3f9b2f31e5ff036594c1da8ff0fe254753b6). h5 requires stopping this affected step. The six explicitly named modules themselves resolve under h5 at HEAD. They are not missing source authorities.

Private prerequisite compiles performed during discovery retain their exact sources, dependency fingerprints and errors; they are focused checks against the loaded objects, not a coherent joint closure or an installed-instance proof. The independently checked original FullFuns source/suffix contexts, small op84 Funs, and ClientPrefix6 do not import BuilderAdmissionExtracted.

Three private aliases were installed during the erroneous workspace selection: AspisR72Sampler.Types, R1Z.BuilderAdmissionExtracted, and AspisR1ProverCommit.Types. Their hashes and joint resolutions are in resolver-object-deviations.json. They receive no canonical closure credit and will be removed as private symlinks; their targets and all shared sources remain unchanged.
