import NKL_CanonicalInstallation
import NKL_CanonicalWindows
set_option autoImplicit false
noncomputable section
namespace NKL_Checks
open Aeneas Aeneas.Std Result AspisR1

inductive Check where
 | cv (bytes : Slice U8) | ec (bytes : Slice U8)
 | view (proof : Slice U8) (i : Usize)
 | scalar (q : Slice U8) (s l : Usize)
 | c1 (q : Slice U8) (s : Usize) | c2 (q : Slice U8) (s l : Usize) | invalid

def scalarInput (bytes : Slice U8) : Option (Array U8 4#usize) :=
 if h:bytes.val.length=4 then some ⟨bytes.val,h⟩ else none

def test : Check→Bool
 | .cv bytes => NKL_CanonicalChildren.compactGood bytes
 | .ec bytes => NKL_CanonicalChildren.echeckGood bytes
 | .view proof i => match NJS_Extract.verifier.candidate.opening proof i with | .ok _=>true | _=>false
 | .scalar q s l => ((NKB_CanonicalScalarLoop.read q s l).bind NKB_CanonicalScalarBridge.scalar).isSome
 | .c1 q s => (NKL_CanonicalKCarrier.selected (NKB_CanonicalTail.window q s)).isSome
 | .c2 q s l => (NKL_CanonicalKCarrier.selected (NKB_CanonicalRange.window q s l)).isSome
 | .invalid => false

def slot (q : Slice U8) (n : Nat) : List Check :=
 let s:=NKB_CanonicalScalarLoop.index n
 ((List.range 26).map fun l=>.scalar q s (NKB_CanonicalScalarLoop.index l)) ++
 [.c1 q s,.c2 q s 0#usize,.c2 q s 1#usize]

def opening (q : Slice U8) : List Check :=
 (List.range 4).flatMap (slot q) ++ [.ec (NKB_CanonicalOpening.trailing q)]

def row (proof : Slice U8) (i : Nat) : List Check :=
 .view proof (NKB_CanonicalScalarLoop.index i) :: match NJS_Extract.verifier.candidate.opening proof (NKB_CanonicalScalarLoop.index i) with
 | .ok q => opening q | _ => [.invalid]

def header (proof : Slice U8) : List Check :=
 [.cv (NKB_CanonicalPrefix.values proof),.ec (NKB_CanonicalPrefix.inactive proof),
  .ec (NKB_CanonicalPrefix.round0 proof),.ec (NKB_CanonicalPrefix.round1 proof)]

def checks (proof : Slice U8) : List Check := header proof ++ (List.range 22).flatMap (row proof)

theorem allFrom (pass : Nat→Bool) (fuel : Nat) :
 NKB_CanonicalPair.allFrom pass 0 fuel=(List.range fuel).all pass := by
 have eq : NKB_CanonicalPair.allFrom pass 0 fuel=true ↔ (List.range fuel).all pass=true := by
  rw [NKL_CanonicalWindows.allFrom]
  simp only [Nat.zero_add,Nat.zero_le,true_implies,List.all_eq_true,List.mem_range]
 cases a:NKB_CanonicalPair.allFrom pass 0 fuel <;> cases b:(List.range fuel).all pass <;> simp_all

theorem slot_test (q : Slice U8) (n : Nat) :
 (slot q n).all test=
 NKB_CanonicalOpening.slot NKB_CanonicalScalarBridge.scalar NKL_CanonicalKCarrier.selected q
  (NKB_CanonicalScalarLoop.index n) := by
 unfold slot NKB_CanonicalOpening.slot NKB_CanonicalTail.accepted
 simp only [List.all_append,List.all_map,List.all_cons,List.all_nil,test,Bool.and_true]
 rw [allFrom]
 simp only [Bool.and_assoc]
 all_goals rfl

theorem opening_test (q : Slice U8) :
 (opening q).all test=
 (NKB_CanonicalPair.allFrom
  (NKB_CanonicalSlotLoop.pass NKB_CanonicalScalarBridge.scalar NKL_CanonicalKCarrier.selected q) 0 4 &&
  NKL_CanonicalChildren.echeckGood (NKB_CanonicalOpening.trailing q)) := by
 unfold opening
 simp only [List.all_append,List.all_flatMap,List.all_cons,List.all_nil,test,Bool.and_true,slot_test]
 rw [allFrom]
 rfl

theorem row_test (proof : Slice U8) (i : Nat) :
 (row proof i).all test=NKB_CanonicalRows.pass NKB_CanonicalScalarBridge.scalar NKL_CanonicalKCarrier.selected
  NKL_CanonicalChildren.echeckGood proof i := by
 unfold row NKB_CanonicalRows.pass NKB_CanonicalRows.accepted
 cases h:NJS_Extract.verifier.candidate.opening proof (NKB_CanonicalScalarLoop.index i) <;>
 simp only [opening_test,List.all_cons,List.all_nil,test,h,Bool.and_true,Bool.true_and,Bool.false_and]

theorem prefix_test (proof : Slice U8) :
 (header proof).all test=NKB_CanonicalPrefix.guard NKL_CanonicalChildren.compactGood NKL_CanonicalChildren.echeckGood proof := by
 simp only [header,List.all_cons,List.all_nil,test,Bool.and_true,NKB_CanonicalPrefix.guard,Bool.and_assoc]

theorem source (proof : Slice U8) :
 (checks proof).all test=
 (NKB_CanonicalPrefix.guard NKL_CanonicalChildren.compactGood NKL_CanonicalChildren.echeckGood proof &&
  NKB_CanonicalPair.allFrom
   (NKB_CanonicalRows.pass NKB_CanonicalScalarBridge.scalar NKL_CanonicalKCarrier.selected
     NKL_CanonicalChildren.echeckGood proof) 0 22) := by
 unfold checks
 simp only [List.all_append,List.all_flatMap,prefix_test,row_test]
 rw [allFrom]

#print axioms allFrom
#print axioms slot_test
#print axioms opening_test
#print axioms row_test
#print axioms prefix_test
#print axioms source
end NKL_Checks
end
