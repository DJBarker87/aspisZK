import NMB_Stage1Post
set_option autoImplicit false
noncomputable section
namespace NMB_Cleanup
open Aeneas Aeneas.Std Result AspisR1 NMB_Stage1Source
/-- Logical destructor occurrences. This retains full values and order, but
makes NO claim that a bump allocator physically frees memory. Native allocator
pointer/capacity events still require the existing allocator interpretation. -/
inductive Drop where
 | checkpoint (value : Bytes)
 | lengthError (account : Nat) (error : PE)
 | bytesValue (account : Nat) (value : Bytes)
 | bytesError (account : Nat) (error : PE)
def account (i : Nat) (a : NMB_Input.Owned) : List Drop :=
 (match a.length with | .Ok _ => [] | .Err error => [.lengthError i error]) ++
 (match a.bytes with | .Ok value => [.bytesValue i value] | .Err error => [.bytesError i error])
def owned (i : Nat) : List NMB_Input.Owned → List Drop
 | [] => []
 | a::rest => account i a++owned (i+1) rest
def G (s : State) : List Drop :=
 (match s.checkpoint with | none=>[] | some value=>[.checkpoint value]) ++ owned 0 s.snapshots.owned
/-- Rust locals are destroyed in reverse declaration order: checkpoint before
owned. Array elements are then destroyed in source index order. -/
theorem saved_first (s : State) (saved : Bytes) :
 G {s with checkpoint:=some saved}=.checkpoint saved::owned 0 s.snapshots.owned := rfl
theorem no_saved (s : State) :
 G {s with checkpoint:=none}=owned 0 s.snapshots.owned := rfl
theorem three (a b c : NMB_Input.Owned) :
 owned 0 [a,b,c]=account 0 a++account 1 b++account 2 c := by
 simp only [owned,List.append_nil,List.append_assoc]
/-- The source snapshot cannot synthesize a String-bearing length error:
its length is the original data length on every normal SDK bracket. -/
theorem snapshot (x : NMB_Input.Input) (a lo hi : Nat) :
 account a (x.snapshot a lo hi)=
 match (x.snapshot a lo hi).bytes with
 | .Ok value=>[.bytesValue a value]
 | .Err error=>[.bytesError a error] := rfl
#print saved_first
#print three
#print axioms saved_first
#print axioms no_saved
#print axioms three
#print axioms snapshot
end NMB_Cleanup
