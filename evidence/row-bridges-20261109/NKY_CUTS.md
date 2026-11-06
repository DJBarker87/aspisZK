# NKY cuts

TX2:216: NKY_K002 positive, K003 actual payload mutation FAIL,
K004 different allocation FAIL. TX2:218: K005 positive, K006 actual payload
mutation FAIL, K007 different allocation FAIL. These proofs instrument the
actual frozen wrapper at its single raw-child boundary. On decoder Err no
Box allocation occurs and InvalidAccountData is returned. On Ok, the pointer
observed immediately after Box::new is the returned Box, fresh from the raw
stack record, and its bump is unchanged. Full payload fields reuse NKP's
20 window pairs, revalidated by immutable inputs, not inferred from pointers.

Every native run has the exact KMX configuration, frozen offline graph and
unchanged lock receipt; no function contract, writable static, field
multiplication or function-pointer observation. Pointer equality is a native
ownership observation, not an inference of payload identity.

The native Kani Box model covers returning allocation. Its allocator abort,
divergence, arbitrary Reservation and source-site binding still require the
Lean allocation action under existing Allocator/P6 trust; local cuts alone do
not close either row. TX1:235 reuses the controlled NJL one-step cut and
NKI's concrete children; literal association is being proved separately.

Final frame binding: Source roots use the actual observed post-state in the
returned Result, not merely a separate logical install lemma. Post.Windows
is the K015/K018 selector/coordinate predicate; FrameObservation proves its
unsigned/bool/array decoding into complete field windows and PostWindows
reconstructs every old live place. The native returned Box supplies the new
payload. Same allocator post and post-reads are joined inside BoxPost.native.
No post-heap endpoint premise or free Ops dictionary is present. K021/K024
also certify the decoded record and raw error types have no destructor, with
payload/different-allocation controls K022/023andK025/026. Thus the source's
error mapping introduces no hidden raw-record/error cleanup, while the Box
ownership transfer remains separately controlled. Exact hashes/quoted
assertions are in NKY_CERTIFICATES.json and the immutable input store.
