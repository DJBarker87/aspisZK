import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
#synth GetElem? (Std.Array U8 48#usize) Usize U8 (fun a i=>i.val<48)
#synth GetElem? (Std.Array U8 48#usize) Usize U8 (fun a i=>i.val<a.val.length)
#print Aeneas.Std.Array
#print Aeneas.Std.Usize
