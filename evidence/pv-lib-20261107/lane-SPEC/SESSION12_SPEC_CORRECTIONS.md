# Session12 local corrections — no frozen endpoint weakening

SPEC-C9 before (WordThreadArc.scopeWord):
```
let panicCell ← C.field panic 0
let .boolean false ← C.field panicCell 0 | none
```
After (NativeBoolArc.scopeWord):
```
let panicCell ← C.field panic 0
let initial ← C.field panicCell 0
match initial with
| .number 0 | .boolean false => pure ()
| _ => none
```
Rust atomic.rs530-531 and the actual v2 boolean load129 both use numeric u8.
AtomicBoolGap.numeric_rejected/image_rejected check the old conflict;
NativeConstructors.initial_scope and AtomicRecheck12.shared_zero recheck the
repair. Packet reply, sparse tails and OWNER laws retain their named rechecks.
The new constructor uses UnsafeCell<u8>; historical NativeKinds.boolCell was
incorrect UnsafeCell<bool> and is UNUSED. All old proved modules are retained.
No row Pre/Post/MachineSpec or T/endpoint field was changed.

SPEC-C10 before (CallbackOperands.captureWords):
```
let runPointer ← SparsePacketHandler.physical C w runReference
```
That resolver requires a registered heap backing, although initialized source
stack references are explicitly admitted by Frozen.References.
After (PhysicalStack12.captureWords):
```
let runPointer ← PhysicalStack12.physical nativeFrame C config w runReference
```
The finite frame names one actual source address and one physical address.
Resolution checks frame activation, source-reference address and initialized
source pointee; other references retain the registered-heap resolver.
StackReferenceGap12 and PhysicalStack12.local_capture check the before/after;
StackRecheck12.callback applies the changed local callback branch with computed
operands. Construction of this physical frame on the actual original history
is STILL OPEN. The native default stack stores are separately checked, not
assumed initialized. No map/decoder-success Prop is added to a row or machine.
