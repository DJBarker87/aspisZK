# R429 actual freeze fold boundary

Previous goal turn made progress: R428 source evidence was committed and pushed as 956b16b46251cc24f0883a17114695ffbb960510. No successful prior job was replayed.

R429 now selects the actual freeze root, with frozen relation_callback.rs SHA256 4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f. It extends the complete R185 command, preserves every existing argument and security setting, and adds only four includes: the specialized slice fold, Iter fields, IS_ZST and SIZE.

Attempt A stopped before Charon at a resource preflight, because an active system Aspis static website had not been accounted for. Its full failure remains saved. Read-only inspection established that the website has a finite 128 MiB MemoryMax. Attempt B corrects the reservation sum without changing the build cap and succeeds; it exposes the fold, fields and IS_ZST but leaves its SIZE dependency opaque. Attempt C changes source-selection scope by adding SIZE, uses a new destination, and succeeds. None of these jobs changes verifier source or runs a benchmark.

Final C: Charon0, GNUtime0, has_errors=false, 14.49s, peakRSS630092KiB, zero swaps; output SHA c7c658bff6e44b6bf8397ea1bc7d37f05f3d33810cffc72ae5eaa0bff06d7465. Actual effective scope caps5G/7G/zero swap/128tasks. Own system website128MiB reservation counted; available memory/other heavy-process gates remain enforced. Every job terminal; no live Lean/extraction job remains.

Function70 is actual specialized slice fold; type42 is transparent Iter<QM31>; type2 is QM31, native x86_64 layout16/align4. Global31 IS_ZST initializer142 compares global32 SIZE with zero. SIZE initializer145 calls intrinsic size_of function153. These are captured source/compiler facts, not a Lean implementation theorem. Keep both branches and all checks/abort/unwind/drop operations until their conditions are justified.

The actual FnMut call in function70's loop has argument0 Move(Local17), not Copy of a persistent receiver. It therefore does not have the helper try_fold receiver-copy shape. Do not repair or replace that call based on R427/R428. Other actual full-freeze operations, including Vec::extend, remain independently open.

Reuse R174/R184/R191 closure/arithmetic results and R193/R195 counted-loop/index bounds. Do not rerun their unchanged checks. These do not prove the source pointer reads, allocation/cursor relation, length/empty tests, size intrinsic, actual unchecked operations, drops/unwinds, or their exact fold binding.

First remaining proposition: source-faithful execution correspondence for the captured actual specialized fold, including its Iter input construction, source-valid immutable slice allocation and pointer/end representation, element reads and lifetimes, closure power restoration, length/empty and size behavior, index arithmetic, final stopping and every legal error/failure/divergence path. Do not assume a whole library fold/extend contract, silently substitute the Nat control model, or claim syntactic lifetimes prove pointer behavior.

Full freeze chronology and Domain inverse execution, complete callback chronology/oracle calls, universal joint C1/H1/G compatibility, published-view simulation/probability losses, coherent pre-beta quotient extraction and optimized-to-source acceptance remain open. End-to-end privacy/security are not proved.
