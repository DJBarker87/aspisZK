# NJJ stubs and trust scope

No field multiplication is executed or proved in Kani. No field stub, contract, stub_verified, writable static or Option<fn>-dependent assertion is introduced. No syscall implementation or SHA is unwound. No new runtime row is used.

The only tool stubs are the supplied KMX_copy_nonoverlapping and KMX_copy_from_slice, from the exact patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. Before every Kani run NJJ_gate.py checks the three supplied KMX source hashes, frozen graph, deployed feature closure and frozen lock, then checks the lock again after the run. Native passing properties require their same-name matched failing control in the same configuration. No custom copy stub.

ReaderLog in NJJ_parent is a local-record child oracle for ONE weights-loop iteration. It records the exact input cursor and supplies the complete Result plus returned cursor and K value. The caller proves the current slot/writeback and nonselected-cell frame for every oracle reply, including all eight Error variants. It is not a closed Reader law, not a root premise, and not native credit until instantiated with the complete CLOSED child Result. Its pairing is the existing NJC_ReaderResults.k / NJC_EReaderResults.e reference laws plus the still OPEN TX2:106 native child association; the OPEN status is retained. Arbitrary new_at is an unconstrained child reply, not an assumption that the real Reader may return arbitrary cursors.

Allocator returning/abort scope is retained. A reserve Bool has not been justified by converting it into another arbitrary carrier. NJJ will not claim that substitution alone discharges the same-invocation allocator item.
