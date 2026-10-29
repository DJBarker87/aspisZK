import R1Z.PV_RDB2F_SoftOuter
namespace R1Z.PV_RDB2F_LoadWrites
open Aeneas Aeneas.Std Result
set_option autoImplicit false
/-- Values after the source zip loop. Each IterMut reference is assigned the
corresponding decoded chunk; old buffer values are never read by the store. -/
def zipStores {A : Type} (old decoded : List A) : List A :=
  List.zipWith (fun _ value => value) old decoded

theorem every_store {A : Type} (old decoded : List A) (length : old.length=decoded.length) :
    zipStores old decoded=decoded := by
  induction old generalizing decoded with
  | nil => cases decoded <;> simp_all [zipStores]
  | cons x old ih =>
    cases decoded with
    | nil => simp at length
    | cons y decoded =>
      have h : old.length=decoded.length := by simpa using length
      simp only [zipStores,List.zipWith_cons_cons]
      exact congrArg (List.cons y) (ih decoded h)

theorem no_stale_word (old decoded : Array U32 16#usize) :
    zipStores old.val decoded.val=decoded.val :=
  every_store old.val decoded.val (old.property.trans decoded.property.symm)

theorem chunk_bounds (i : Nat) (h : i<16) : 4*i+4≤64 := by omega

theorem chunk_exact (block : Array U8 64#usize) (i : Nat) (h : i<16) :
    ((block.val.drop (4*i)).take 4).length=4 := by
  simp only [List.length_take,List.length_drop,block.property]
  change min 4 (64-4*i)=4
  omega

/-- The native chunks_exact iterator and output mutable iterator both run sixteen
steps; there is no short zip and no residual source byte on the admitted block. -/
theorem zip_trip_count : min 16 (64/4)=16 ∧ 64%4=0 := by decide

#print axioms every_store
#print axioms no_stale_word
#print axioms chunk_bounds
#print axioms chunk_exact
#print axioms zip_trip_count
end R1Z.PV_RDB2F_LoadWrites
