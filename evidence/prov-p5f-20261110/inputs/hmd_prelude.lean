/-- HM-D (trust row, CoreArraySliceOps member): core::array::from_fn, the array whose i-th element is
f(i), f evaluated in index order 0..N-1 with the FnMut state threaded.  Modelled by the gate's own
AspisR1.OraclePortStdBuilder.fromFn; PCWP_FromFnSem proves the gate model satisfies that semantics.
The fresh emission declares this name as an external axiom; here it is instantiated with the HM-D model. -/
@[reducible] def core.array.from_fn {T F : Type} (N : Std.Usize)
  (opsfunctionFnMutFTupleUsizeTInst : core.ops.function.FnMut F Std.Usize T) :
  F → Result (Array T N) :=
  fun f => AspisR1.OraclePortStdBuilder.fromFn N opsfunctionFnMutFTupleUsizeTInst f
