import NGA_Converter
import RPv_AspisR1_PoseidonPreparedKaratsubaAggregateAlgebra
set_option autoImplicit false
namespace NGA_ChannelAlgebra
open Aeneas Aeneas.Std Result NGA_Cell NGA_Converter
abbrev Probe := NGA_Cache.Q
abbrev decodeQ := AspisR1.ExtractedMaskQM31Exact.decode

def component (x : Probe) (i : Fin 3) : C :=
 if i=0 then (decodeQ x).re else if i=1 then (decodeQ x).im else (decodeQ x).re+(decodeQ x).im

def channels (x : Probe) (d : Cell) : M :=
 let c := component x d.1
 if d.2=0 then c.re else if d.2=1 then c.im else c.re+c.im

theorem row_add (s t : State) (i : Fin 3) :
 row (fun d => s d+t d) i=row s i+row t i := by
 apply QuadraticAlgebra.ext <;> simp only [row,QuadraticAlgebra.re_add,QuadraticAlgebra.im_add] <;> ring

theorem add (s t : State) : interpret (fun d => s d+t d)=interpret s+interpret t := by
 apply QuadraticAlgebra.ext <;> simp only [interpret,row_add,QuadraticAlgebra.re_add,QuadraticAlgebra.im_add] <;> ring

theorem zero : interpret (fun _ => 0)=0 := by
 apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;> simp [interpret,row] <;> ring

theorem row_product (x y : Probe) (i : Fin 3) :
 row (fun d => channels x d*channels y d) i=component x i*component y i := by
 apply QuadraticAlgebra.ext
 · simp [row,channels,QuadraticAlgebra.re_mul];ring
 · simp [row,channels,QuadraticAlgebra.im_mul]
   ring

theorem product (x y : Probe) :
 interpret (fun d => channels x d*channels y d)=decodeQ x*decodeQ y := by
 apply QuadraticAlgebra.ext
 · simp [interpret,row_product,component,QuadraticAlgebra.re_mul,
     AspisV8R15.ExactTowerBase.qm31R]
 · simp [interpret,row_product,component,QuadraticAlgebra.im_mul]
   ring

#print axioms row_add
#print axioms add
#print axioms zero
#print axioms row_product
#print axioms product
end NGA_ChannelAlgebra
