# Slice havoc pilot (not yet admitted for parent use)

K064 proves the actual auxiliary point-store contract for arbitrary bytes,
all nonempty lengths≤13831 and arbitrary selected index/word. It returns Unit,
modifies only dst and constrains only dst[probe]=word. Under stub_verified the
other dst bytes are free. The recorded word is arbitrary; NMP_ByteHavocLaw
proves every desired post-state of the same length has a suitable word.
This is a generator utility, never a source child's functional law or a field
multiplication stub. It adds no runtime trust row; contracts remain the
explicitly retained P6/D188 tool reclassification.

Before ANY parent uses it: inverted ensures FAIL, weak-contract proof PASS,
unimplied caller assertion FAIL under stub_verified while PASS on the real
body, modifies violation FAIL, verified caller PASS and matched corrupted
caller FAIL. The unimplied test initializes the selected byte to known zero,
so its failure specifically requires slice data havoc rather than a free
initial byte. All live/static state is local. Exact KMX and deployed features
remain unchanged. Controls have not yet completed; no parent use is credited.

Dynamic slice interface: K064 positive, K065 inverse correctly fails, K066 weak positive, K067 real-body positive, K068 compiler ICE before verification, K069 outside-modifies correctly fails. Thus NOT admitted. Changed fixed-array interfaces at13831 and928 are being independently calibrated. K070 fixed13831 positive passed; all caller controls still pending. Prepare source now drafts use, but no prepare native claim is admitted before calibration completes.

K090: actual prepare branch_3 selected correctly, CBMC status139 before any verification check. Fixed-array contract calibration on standalone stack arrays does NOT admit this heap-subwindow/nested-stub context. Exact cause unisolated. Parent use is withdrawn; new prepare shape assigns a full arbitrary typed byte array at both Ok/Err mutation cuts with exact KMX stubs, not a custom copy stub. No cap/time increase or unchanged replay.
