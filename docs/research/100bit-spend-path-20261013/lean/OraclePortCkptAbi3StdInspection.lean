import OraclePortCkptAbi2Vec
import Aeneas.Std.VecIter

/-! Inspect the imported std boundary before asserting physical allocation
or source owned-iterator semantics. No allocator hypothesis is introduced. -/
#print Aeneas.Std.alloc.vec.Vec.with_capacity
#print Aeneas.Std.alloc.vec.into_iter.IntoIter
#print Aeneas.Std.alloc.vec.Vec.extend_from_slice
#print axioms AspisR1.OraclePortCkptAbi2Vec.push_exact
#print axioms AspisR1.OraclePortCkptAbi2Vec.append_exact
