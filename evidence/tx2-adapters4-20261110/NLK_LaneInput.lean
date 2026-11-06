import NLK_LaneGeometry
set_option autoImplicit false
noncomputable section
namespace NLK_LaneInput
open Aeneas Aeneas.Std Result
structure Sized where
  bytes : Slice U8
  length : bytes.val.length=768

def byte (p : Sized) (i : Nat) : U8 := p.bytes.val[i]?.getD (0#u8)

def window32 (p : Sized) (start : Nat) (bound : start+32≤768) : Array U8 32#usize :=
 ⟨(p.bytes.val.drop start).take 32,by
   simp only [List.length_take,List.length_drop,p.length]
   change min 32 (768-start)=32
   omega⟩

def sequence (p : Sized) : Array U8 8#usize :=
 ⟨(p.bytes.val.drop 88).take 8,by
   simp only [List.length_take,List.length_drop,p.length]
   decide⟩

def master (p : Sized) : Array U8 32#usize := window32 p 40 (by decide)
def root (p : Sized) : Array U8 32#usize := window32 p 96 (by decide)
def frontier (p : Sized) (level : Fin 20) : Array U8 32#usize :=
 window32 p (128+32*level.val) (by omega)

theorem master_bytes (p : Sized) : (master p).val=(p.bytes.val.drop 40).take 32 := rfl
theorem root_bytes (p : Sized) : (root p).val=(p.bytes.val.drop 96).take 32 := rfl
theorem frontier_bytes (p : Sized) (level : Fin 20) :
 (frontier p level).val=(p.bytes.val.drop (128+32*level.val)).take 32 := rfl

theorem window_domain (p : Sized) (start : Nat) (bound : start+32≤768) :
 (window32 p start bound).val.length=32 := (window32 p start bound).property

theorem byte_exists (p : Sized) (i : Nat) (small : i<768) :
 ∃ b, p.bytes.val[i]?=some b := by
 have hi : i<p.bytes.val.length := by rw [p.length];exact small
 exact ⟨p.bytes.val[i]'hi, List.getElem?_eq_getElem hi⟩

#print axioms master_bytes
#print axioms root_bytes
#print axioms frontier_bytes
#print axioms window_domain
#print axioms byte_exists
end NLK_LaneInput
