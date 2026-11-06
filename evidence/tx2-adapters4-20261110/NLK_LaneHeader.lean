import NLK_LaneInput
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace NLK_LaneHeader
open Aeneas Aeneas.Std Result NLK_LaneInput
abbrev PE := NKF_BoxModel.PE
attribute [local instance] Classical.propDecidable
def formatBinding : List U8 := [65#u8,83#u8,80#u8,73#u8,83#u8,70#u8,79#u8,82#u8,69#u8,83#u8,84#u8,56#u8,2#u8,2#u8,2#u8,8#u8,1#u8,20#u8,1#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]

def header (p : Sized) : Prop :=
 p.bytes.val.take 4=[65#u8,83#u8,76#u8,56#u8] ∧
 byte p 4=2#u8 ∧ (byte p 5).val<8 ∧ byte p 6=8#u8 ∧ byte p 7=20#u8 ∧
 (p.bytes.val.drop 8).take 32=formatBinding ∧
 (∀ b, b∈(p.bytes.val.drop 73).take 7 → b=0#u8)

def treeHeader (p : Sized) : Prop :=
 (p.bytes.val.drop 80).take 4=[65#u8,83#u8,80#u8,84#u8] ∧
 byte p 84=1#u8 ∧ byte p 85=20#u8 ∧ byte p 86=3#u8 ∧ byte p 87=1#u8

structure Fields where
 bump : U8
 master : Array U8 32#usize
 lane : U8
 next : U64

def fields (p : Sized) : Fields :=
 ⟨byte p 72,master p,byte p 5,core.num.U64.from_le_bytes (sequence p)⟩

def AdmittedPrefix (p : Sized) : Prop :=
 header p ∧ master p≠Array.repeat 32#usize 0#u8 ∧ treeHeader p ∧
 (fields p).next.val≤1048576

/-- Literal source guard order before the root call; every rejected path has
no decoder/allocator event. All slices have domains supplied by Sized. -/
def sourcePrefix (p : Sized) : core.result.Result Fields PE :=
 if header p then
  if master p=Array.repeat 32#usize 0#u8 then .Err .InvalidAccountData
  else if treeHeader p then
   if (fields p).next.val≤1048576 then .Ok (fields p) else .Err .InvalidAccountData
  else .Err .InvalidAccountData
 else .Err .InvalidAccountData

def parse (p : Sized) : core.result.Result Fields PE :=
 if AdmittedPrefix p then .Ok (fields p) else .Err .InvalidAccountData

theorem source_order (p : Sized) : sourcePrefix p=parse p := by
 by_cases h : header p <;>
 by_cases m : master p=Array.repeat 32#usize 0#u8 <;>
 by_cases t : treeHeader p <;>
 by_cases n : (fields p).next.val≤1048576 <;>
 simp only [sourcePrefix,parse,AdmittedPrefix,ne_eq,eq_self,h,m,t,n,not_true_eq_false,not_false_eq_true,
   and_false,and_true,false_and,true_and,if_true,if_false]

theorem rejected (p : Sized) (bad : ¬ AdmittedPrefix p) :
 sourcePrefix p=.Err .InvalidAccountData := by
 rw [source_order];exact if_neg bad

theorem admitted (p : Sized) (good : AdmittedPrefix p) :
 sourcePrefix p=.Ok (fields p) := by
 rw [source_order];exact if_pos good

theorem source_fields (p : Sized) :
 (fields p).bump=byte p 72 ∧ (fields p).master.val=(p.bytes.val.drop 40).take 32 ∧
 (fields p).lane=byte p 5 ∧
 (fields p).next=core.num.U64.from_le_bytes (sequence p) :=
 ⟨rfl,rfl,rfl,rfl⟩

#print source_order
#print axioms source_order
#print axioms rejected
#print axioms admitted
#print axioms source_fields
end NLK_LaneHeader
