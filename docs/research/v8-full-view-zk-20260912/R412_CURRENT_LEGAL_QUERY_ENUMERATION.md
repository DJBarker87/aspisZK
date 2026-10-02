# R412: legal-query finite enumeration

The successful focused compile proves that every `ResultValid` success list has a unique representation as a legal injection `Fin 22 → Fin (2^18)`, and that an observer which vanishes on every error can be expanded over the finite set of legal query tuples. The theorem covers the `Except Nat (List Nat)` result interface under the existing `Q22SamplerInvariants.ResultValid` premise; it does not add probability or source-execution premises.

The promoted source retains an earlier comment describing the file as uncompiled. That comment is preserved byte-for-byte from the source snapshot; the successful run recorded here supersedes that historical wording. The exact promoted source matches the successful compiler input (SHA-256 `2a950c0cbb915c496a8ba0ad4738f35d73d1381693b07183e08d57f6a1855a36`).

The successful run was target `AspisV8R19/R412LegalQueryEnumeration.lean`, exit status 0, wall time 1.41 s, peak Lean-child RSS 3,235,376 KiB, swap 0, at source revision `c145fb14be60e3b2553713927228ac62876dbab2`. The run used `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, and Lean flags `-j1 -M4500`. RSS is GNU time's Lean-child measurement; the wrapper's reported memory peak is a separate measurement.

All five complete `#print axioms` reports contain only `propext`, `Quot.sound`, and (for the final finite-sum theorem) `Classical.choice`. Two earlier failed proof drafts are retained as rejected history and are not evidence for the result. The import `AspisV8R19.Q22SamplerInvariants` was recorded at SHA-256 `a4663c405ca28515bd8d7e370d2146017b067286845329273e77bd088c0fa24b`; the saved source copy is in the evidence bundle. The compiler's cached environment was reused; cache artifact identities were not part of the original run receipt and are separately enumerated in the bundle rather than inferred from the receipt.

The next formal step is to establish the candidate kernel's valid support and linearity, then normalize its successful kernel over `LegalQuery`. The actual shared-oracle source correspondence remains open. This result makes no claim about probabilities, source freshness, publication, or security.
