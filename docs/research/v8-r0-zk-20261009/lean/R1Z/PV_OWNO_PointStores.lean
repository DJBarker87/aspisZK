import R1Z.PV_OWNO_SampleEight
import R1Z.PV_OWNL_Inputs
set_option autoImplicit false
namespace R1Z.PV_OWNO_PointStores
open Aeneas Aeneas.Std PV_OWNK_TowerCanon
attribute [local irreducible] PV_OWNL_SampleWord.u32

/-- Source writes to the ten-coordinate point, including the terminal
challenge store. Sample indices are precisely the 28 interpolation samples. -/
inductive Write where
 | sample (index : Fin 10) (sample : Fin 28)
 | boolean (index : Fin 10) (bit : Bool)
 | challenge (index : Fin 10) (rank : List U32)

def value (combine : U64 → U32 → U64) : Write → Q
 | .sample _ s => PV_OWNL_Inputs.lift (PV_OWNL_SampleWord.u32 s.val)
 | .boolean _ b => if b then one else zero
 | .challenge _ rank => PV_OWNO_SampleEight.sample combine rank

def index : Write → Nat
 | .sample i _ | .boolean i _ | .challenge i _ => i.val

theorem value_canonical (combine : U64 → U32 → U64) (w : Write) :
 Canon (value combine w) := by
 cases w with
 | sample i s =>
  apply PV_OWNL_Inputs.lift_canon
  change s.val % 4294967296 < 2147483647
  have hs := s.isLt
  rw [Nat.mod_eq_of_lt (by omega)]
  omega
 | boolean i b => cases b <;> first | exact zero_canon | exact one_canon
 | challenge i rank => exact PV_OWNO_SampleEight.sample_canonical combine rank

def store (combine : U64 → U32 → U64) (point : List Q) (w : Write) : List Q :=
 point.set (index w) (value combine w)

theorem store_canonical (combine : U64 → U32 → U64) (point : List Q) (w : Write)
 (hp : ∀ q ∈ point, Canon q) : ∀ q ∈ store combine point w, Canon q :=
 PV_OWNL_HelperRows.store_canonical point (index w) (value combine w) hp (value_canonical combine w)

def run (combine : U64 → U32 → U64) (writes : List Write) : List Q :=
 writes.foldl (store combine) (List.replicate 10 zero)

theorem fold_canonical (combine : U64 → U32 → U64) (writes : List Write)
 (point : List Q) (hp : ∀ q ∈ point, Canon q) :
 ∀ q ∈ writes.foldl (store combine) point, Canon q := by
 induction writes generalizing point with
 | nil => exact hp
 | cons w ws ih => exact ih _ (store_canonical combine point w hp)

theorem run_canonical (combine : U64 → U32 → U64) (writes : List Write) :
 ∀ q ∈ run combine writes, Canon q := by
 apply fold_canonical
 intro q hq
 have he := List.eq_of_mem_replicate hq
 cases he
 exact zero_canon

theorem fold_length (combine : U64 → U32 → U64) (writes : List Write) (point : List Q) :
 (writes.foldl (store combine) point).length = point.length := by
 induction writes generalizing point with
 | nil => rfl
 | cons w ws ih =>
  rw [List.foldl_cons,ih]
  simp only [store,List.length_set]

theorem run_length (combine : U64 → U32 → U64) (writes : List Write) :
 (run combine writes).length = 10 := by
 rw [run,fold_length,List.length_replicate]

#print axioms value_canonical
#print axioms store_canonical
#print axioms fold_canonical
#print axioms run_canonical
#print axioms fold_length
#print axioms run_length
end R1Z.PV_OWNO_PointStores
