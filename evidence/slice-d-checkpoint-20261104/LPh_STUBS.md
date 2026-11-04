# NGC selected stubs and retained interfaces

No field-multiplication stub is used. No selected harness uses stub_verified, a function contract, a writable static or a function-pointer/Option<fn> observer. Local oracle records are explicit &mut arguments. No SHA implementation is unwound.

| Native substitution | Paired Lean law / domain | Disposition |
|---|---|---|
| `heap::filled -> reject_filled<T>` in actual frozen `Accumulator::new(S2)` | `NGC_Initialization.rejection`, `heap_result`; exact n=64, zeroK; source heap's reservation-failure model is Allocation | K094/095 positive/control; only Allocation path, success supplied by separate full-Result local-record source-fission K004/005 |
| heap reserve/resize local record interfaces | `NGC_ReferenceValues.heap`, `resize_empty`, `NGC_Initialization.heap_result`; SAME actual reservation Result, pure Clone, owned same reply allocation | Ruling(y) source-erasure, exact argument/order/Result/native frame; actual reserve prefixes and Clone identity checked for the four frozen monomorphs. Std allocation/resize capacity/ownership/cleanup realization retained. These are not claims that allocation is infallible. |
| hashv local syscall record | `NGC_DigestBridge.observed`, `forwarding`, `checkpoint_oracle`; SAME ordered borrowed descriptors, full arbitrary32-byte reply | K082/083 and copy controls084/085. Value=H is retained RuntimeSha256Value, not a new theorem. |
| prescribed copy/realloc/slice-copy replacements | `KMX_CopyMeaning` append/value/frame laws, `NGC_AppendFrame`; exact KMX patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67 | Same patch/gate/features/lock per selected positive and failing copy control; no private copy stub. |

Heap reference/model equality is full length/content/error on both reservation outcomes. The native ordinary-owned resize window is one actual step at physical length1→2, with arbitrary old/new payload and observed old/written cell, pointer stability and a matched failure. It does not itself prove a32768-element native execution or an arbitrary generic `T:Copy` Clone law. General length and value composition uses `NGC_FillInduction` and the pinned emitted Std resize law. Std/allocator/source-to-ELF realization and P6/D188 option-A transport remain retained, explicitly, rather than declared discharged.
