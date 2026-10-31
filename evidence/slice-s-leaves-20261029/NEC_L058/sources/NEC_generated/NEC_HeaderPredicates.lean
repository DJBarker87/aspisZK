import NEC_HeaderIndex
set_option autoImplicit false
namespace NEC_HeaderPredicates
open Aeneas Aeneas.Std Result

def byte (a : Array U8 48#usize) (i : Usize) (bound : i.val<48) : U8 :=
 a.val[i.val]'(by simpa [a.property] using bound)

theorem byte_spec (a : Array U8 48#usize) (i : Usize) (bound : i.val<48) :
 Array.index_usize a i=ok (byte a i bound) := NEC_HeaderIndex.index_read a i bound

def magic (a : Array U8 48#usize) : Bool :=
 decide (byte a 0#usize (by decide)=65#u8) &&
 decide (byte a 1#usize (by decide)=83#u8) &&
 decide (byte a 2#usize (by decide)=80#u8) &&
 decide (byte a 3#usize (by decide)=76#u8) &&
 decide (byte a 4#usize (by decide)=73#u8) &&
 decide (byte a 5#usize (by decide)=86#u8) &&
 decide (byte a 6#usize (by decide)=69#u8) &&
 decide (byte a 7#usize (by decide)=49#u8)

def binding0 (a : Array U8 48#usize) : Bool :=
 decide (byte a 16#usize (by decide)=65#u8) &&
 decide (byte a 17#usize (by decide)=83#u8) &&
 decide (byte a 18#usize (by decide)=80#u8) &&
 decide (byte a 19#usize (by decide)=80#u8) &&
 decide (byte a 20#usize (by decide)=65#u8) &&
 decide (byte a 21#usize (by decide)=73#u8) &&
 decide (byte a 22#usize (by decide)=82#u8) &&
 decide (byte a 23#usize (by decide)=49#u8)

def binding1 (a : Array U8 48#usize) : Bool :=
 decide (byte a 24#usize (by decide)=1#u8) &&
 decide (byte a 25#usize (by decide)=20#u8) &&
 decide (byte a 26#usize (by decide)=21#u8) &&
 decide (byte a 27#usize (by decide)=7#u8) &&
 decide (byte a 28#usize (by decide)=1#u8) &&
 decide (byte a 29#usize (by decide)=1#u8) &&
 decide (byte a 30#usize (by decide)=1#u8) &&
 decide (byte a 31#usize (by decide)=1#u8)

def binding2 (a : Array U8 48#usize) : Bool :=
 decide (byte a 32#usize (by decide)=0#u8) &&
 decide (byte a 33#usize (by decide)=0#u8) &&
 decide (byte a 34#usize (by decide)=0#u8) &&
 decide (byte a 35#usize (by decide)=0#u8) &&
 decide (byte a 36#usize (by decide)=0#u8) &&
 decide (byte a 37#usize (by decide)=0#u8) &&
 decide (byte a 38#usize (by decide)=0#u8) &&
 decide (byte a 39#usize (by decide)=0#u8)

def binding3 (a : Array U8 48#usize) : Bool :=
 decide (byte a 40#usize (by decide)=0#u8) &&
 decide (byte a 41#usize (by decide)=0#u8) &&
 decide (byte a 42#usize (by decide)=0#u8) &&
 decide (byte a 43#usize (by decide)=0#u8) &&
 decide (byte a 44#usize (by decide)=0#u8) &&
 decide (byte a 45#usize (by decide)=0#u8) &&
 decide (byte a 46#usize (by decide)=0#u8) &&
 decide (byte a 47#usize (by decide)=0#u8)

#print axioms byte_spec
end NEC_HeaderPredicates
