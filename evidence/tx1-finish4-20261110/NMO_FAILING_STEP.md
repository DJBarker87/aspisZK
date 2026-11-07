# NMO first unresolved native step

Target not yet established. This is a cut-mechanism finding, not a counterexample to the frozen verifier.

NMO-F1: r1_semantic.rs:251 calls state_only_selected_mask_value with references to freshly copied low/high arrays and the returned alpha array plus a value blind. At :258, QM31::mul(self, rhs) and both QM31::add(self, rhs) consume 16-byte values by value. These signatures receive neither H nor a context pointer. The current validated (bl) logger through H or Prefix cannot record all exact caller operands and independent arbitrary replies for these calls. The parent-local temporary arrays do not carry a valid pointer to the harness log. Encoding a logger pointer in operand limbs would narrow the caller domain and is not used.

No writable static, stack-provenance guess, arbitrary field pointer, modified frozen signature or function body is used. No field product is proved in Kani, and no constrained arithmetic stub is silently substituted for the job's explicit full-type havoc requirement. All independent prefix partitions and Lean-only domain work continue. The CUTMAP classifies this literal channel gap under (bl)(4). Any future root still needs a validated native relation that covers these exact calls.

The missing deliverable is an admissible native scalar-cut/temporary-array channel or a validated actual-parent relational cut that retains their exact operands and full independent replies. Skipping it would reclassify additional parent execution into P6 trust and requires a lead decision; this job adds no trust item. No child Result or whole-parent endpoint is admitted as a root premise.
