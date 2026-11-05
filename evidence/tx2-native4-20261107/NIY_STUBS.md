# NIY stubs and domains

TX2:065 OPEN. No new field-multiplication, SHA, function-contract or stub_verified proof is used. No writable static or function-pointer-dependent native credit is claimed.

All selected native harnesses use exactly KMX_copy_stubs.patch, SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. Provided KMX_copy_nonoverlapping and KMX_copy_from_slice are the only kani::stub replacements in these harnesses. Their supplied value/frame laws are KMX_CopyMeaning.loop_spec/copy_prefix/copy_frame/append_spec/realloc_prefix; NID's committed window/all64/frame instantiations are retained. Every copy-dependent local family needs a semantic corruption failure under the same patch/configuration; timeout is never a control.

The scan-prefix Log.enter is an explicit local-record oracle in a source cut, not a proof of the child: full8 Error constructors, exact slice descriptor/mode and only the local log modified. The child results remain arbitrary until the CLOSED check_values/echeck laws are installed at those same calls. Its tail Result is arbitrary and gives no whole canonical_scan credit. No static log or fabricated borrowed reference is used.

The other new native functions execute the actual frozen Reader::raw/e/k, std reserve/iterator/Box/Vec operations or actual opening getter. No arithmetic result is stubbed. Constructor capacity64/source occurrence and SAME reserve/resize/read producer remain explicit caller-domain findings; the model continuation equalities do not discharge them. Runtime/allocator/Std/P6/D188 and cryptographic assumptions remain retained. Native cut transcription is optionA reclassification, never removal or a new trust row. RuntimeCpiReadonlyEntry7 is PENDING and unused.
