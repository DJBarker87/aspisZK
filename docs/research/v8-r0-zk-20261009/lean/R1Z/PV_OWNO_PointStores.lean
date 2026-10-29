import R1Z.PV_OWNO_SampleEight
import R1Z.PV_OWNL_Inputs
import R1Z.PV_OWNO_Builder
import R1Z.PV_OWNM_V239
set_option autoImplicit false
namespace R1Z.PV_OWNO_PointStores
open Aeneas Aeneas.Std PV_OWNK_TowerCanon PV_OWNO_HelperArrays
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
  unfold PV_OWNL_SampleWord.u32
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
/-- The consuming Input uses the same successful column vector and reached
point state. This is a carrier map, not a replacement definition of native. -/
def input (pub : PV_OWNM_V239.Public) (site : PV_OWNM_V239.Site)
 (combine : U64 → U32 → U64) (writes : List PV_OWNO_PointStores.Write)
 (columns : List (List Q)) : PV_OWNM_V239.Input :=
 ⟨pub,site,PV_OWNO_PointStores.run combine writes,columns⟩

theorem canon_transport (q : Q) (h : Canon q) : PV_OWNM_V239.Canon q :=
 ⟨h.1.1,h.1.2,h.2.1,h.2.2⟩

/-- ActualInput for the source-stage model, with complete error-preserving
builder execution as its premise. Native source/carrier association must be
checked separately before this can be installed at the deployed consumer. -/
theorem of_builder_execution {E : Type} (publicError imbalance : E)
 (inverse : Q → Option Q) (base : Aeneas.Std.Array (List U32) 26#usize)
 (d g : Aeneas.Std.Array Q 1024#usize)
 (setup : Unit → Except E (Q × Q)) (registry : Q → Except E (List CopyRow))
 (balanced : List Q → Bool) (finish : List Q → Except E Unit) (columns : List (List Q))
 (built : PV_OWNO_Builder.build publicError imbalance inverse base d g setup registry balanced finish = .ok columns)
 (pub : PV_OWNM_V239.Public) (site : PV_OWNM_V239.Site)
 (combine : U64 → U32 → U64) (writes : List PV_OWNO_PointStores.Write) :
 PV_OWNM_V239.PV_OWNM_Link_ActualInput PV_OWNJ_Points.statement_points
  (input pub site combine writes columns) := by
 have hc := PV_OWNO_Builder.successful_canonical publicError imbalance inverse base d g
  setup registry balanced finish columns built
 have hp := PV_OWNO_PointStores.run_canonical combine writes
 have hl := PV_OWNO_PointStores.run_length combine writes
 refine ⟨hl,?_,?_⟩
 · intro p hmem
   refine ⟨(PV_OWNJ_Points.point_lengths _ p hmem).trans hl,?_⟩
   intro q hq
   exact canon_transport q (PV_OWNL_Inputs.statement_points_canon _ hp p hmem q hq)
 · intro c hmem q hq
   exact canon_transport q (hc c hmem q hq)

#print axioms canon_transport
#print axioms of_builder_execution
end R1Z.PV_OWNO_PointStores
