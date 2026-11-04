# Native source consumer after the scalar guards

The required provider is **pv-evhB4's shared owner relation** between source Vec/RawVec pointer and capacity and the stateful allocator world, preserved through RawVec operations. Its actual declaration is not merged in this worktree. No substitute owner relation, invented declaration name, endpoint hypothesis, or T field is introduced here. The lead merges that provider when it lands.

The pointer-validity step must consume that declaration at each actual array/slice/Vec source event, with the source element type/layout, pointer provenance and alignment, live region, capacity and initialized length. Scalar index<length certificates supply only the numeric part. They do not create a valid region or establish a native reference read/write.

After that step, restoration must use the same owner and allocator-world state to return the actual backward continuations for array IndexMut, slice copies, iterators and drain callbacks. Partial initialization must retain the initialized prefix and pending callback value until the exact source store commits. Error and unwind paths must drop exactly the initialized prefix, retain the live authority needed by the allocator, and account for Guard drop and final mem::forget. No always-success allocator, guaranteed thread/stack resource or witness-independent failure is assumed.

The current local array/slice wrappers, initializer control lemmas and scalar guards remain useful predecessors. They do not discharge these native obligations or any of the16 opaque instances by themselves. Native initializer/global reads and actual dictionary composition follow, with the source statement order and all error/drop branches intact.

Exact residual, unchanged:

`forall p claims point c, ops.op227 p claims point c = PV_B3P_Install227.transport (PV_B3P_TopDown13227.source_continuation base (PV_B3P_Closure557227.composed_ports557 base) p claims point c)`.

Do not choose Install227.actual, source_install15 or a model dictionary as the actual deployed witness. Consume selected_callback_residual557/runjoin only after the actual DeployedWrapper557 instance exists. Privacy target not established.
