# Stage 3: real decoder/write steps

K013,K014,K015 pass all980 checks each. These checks execute BOTH full real decode_k::<29> calls, comparing the exact shipped pointer/write expression to the safe row setter, with arbitrary3717-byte record contents and arbitrary initialized prior QM31 rows. No decoder stub, symbolic success assumption, byte-havoc return or chosen decoder outcome is used. The rows initially uninitialized in the native buffer are never inspected before initialization. On rejection the initialized prefix is compared; on success it includes the written row. K015 also performs the actual assume_init conversion and compares an arbitrary cell of the complete native Box. These are three one-iteration source gates, NOT the complete caller equality.

K013: exit0,62.090849680s,3781384 KiB RSS,swap0.
K014: exit0,69.324924166s,3831788 KiB RSS,swap0.
K015: exit0,83.344794112s,4177320 KiB RSS,swap0.
K011: complete caller's static932-byte short-record rejection passes918 checks; exit0,3.579204361s,358680 KiB,swap0. This is an error-path gate, not accepted-prefix coverage.

The actual native uninit/pointer-write caller and safe reference remain source-pinned and unchanged. K007-K010 and K012 remain excluded attempts: timeout or manual formula-growth stop, never a shipped-source counterexample. No unchanged killed/timed-out command was repeated. K011 isolates the static length gate; later work splits complete caller characterization rather than raising the cap.

L013 proves NP6_ResultUniqueness.unique: a shared allocator outcome, every successful scalar value, and the actual first failing field uniquely determine the entire abstract Result. Its only axiom is Quot.sound. Two local non-vacuity theorems have no axioms. This is a mathematical composition theorem; it is NOT a native source instance. Native/reference concrete unary characterizations still need checking. K016 attempts that complete native characterization and remains pending/excluded until its result is collected.

Ledger delta: zero rows removed, zero new trust items. All original joint theorem premises stay retained as in STAGE2. The checked native step gates narrow the P6 source gap, but do not install an unproved whole-caller interpretation. No shipped-file change, ELF rebuild, package replay or source adoption.
