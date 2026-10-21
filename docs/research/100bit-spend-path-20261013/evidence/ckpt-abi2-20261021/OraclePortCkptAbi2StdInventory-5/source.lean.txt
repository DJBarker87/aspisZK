import OraclePortCkptAbi2Unwrap

/-! The imported Vec is a bounded list. Its success theorems describe values,
not physical allocator availability or Rust drop/deallocation behavior. -/
#print Aeneas.Std.alloc.vec.Vec
#print Aeneas.Std.alloc.vec.Vec.push
#print axioms AspisR1.OraclePortCkptAbi2Unwrap.savedTen_panic_unreachable
