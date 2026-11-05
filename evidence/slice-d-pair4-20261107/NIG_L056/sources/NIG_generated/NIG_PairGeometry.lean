import NIG_Geometry
import NIG_PairInputs
set_option autoImplicit false
namespace NIG_PairGeometry
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

theorem length {T:Type} (s:Slice T) (n:Usize) (h:s.val.length=n.val):Slice.len s=n:=
 UScalar.eq_of_val_eq h

theorem alpha_length (p:verifier.Prepared):
 Slice.len (FIo_Install.toSlice p.alpha.to_slice)=2#usize:=by
 apply length
 change (p.alpha.val.map FIo_Install.toE).length=2
 rw [List.length_map,p.alpha.property]
 rfl

theorem message_cells (f:Slice U8) (width:f.val.length=2048):
 (Slice.len f / 32#usize:Result Usize)=ok 64#usize:=by
 rw [length f 2048#usize width]
 rfl

theorem expected (p:verifier.Prepared):
 FIo_Native.weights.Weights.pair_loop0 {start:=0#usize,«end»:=Slice.len (FIo_Install.toSlice p.alpha.to_slice)} 1024#usize=ok 64#usize:=by
 rw [alpha_length]
 exact NIG_Geometry.expected
#print axioms length
#print axioms alpha_length
#print axioms message_cells
#print axioms expected
end NIG_PairGeometry
