import R1Z.PV_OWNO_PointStores
set_option autoImplicit false
namespace R1Z.PV_OWNP_PointArray
open Aeneas Aeneas.Std PV_OWNK_TowerCanon
abbrev Point := Aeneas.Std.Array Q 10#usize

/-- Ten initialized stack entries, before the first round. -/
def initial : Point := ⟨List.replicate 10 zero, by rfl⟩

/-- In-bounds direct array store. The index is retained, rather than an
unchecked List.set whose out-of-range case silently leaves the list intact. -/
def store (point : Point) (i : Fin 10) (q : Q) : Point :=
 ⟨point.val.set i.val q, by simpa only [List.length_set] using point.property⟩

def index (w : PV_OWNO_PointStores.Write) : Fin 10 :=
 match w with
 | .sample i _ | .boolean i _ | .challenge i _ => i

def step (combine : U64 → U32 → U64) (point : Point)
 (w : PV_OWNO_PointStores.Write) : Point :=
 store point (index w) (PV_OWNO_PointStores.value combine w)

def run (combine : U64 → U32 → U64) (writes : List PV_OWNO_PointStores.Write) : Point :=
 writes.foldl (step combine) initial

theorem index_bound (p : Point) (i : Fin 10) : i.val < p.val.length := by
 have h := p.property
 change p.val.length = 10 at h
 rw [h]
 exact i.isLt

theorem store_view (p : Point) (i : Fin 10) (q : Q) :
 (store p i q).val = p.val.set i.val q := rfl

theorem step_view (combine : U64 → U32 → U64) (p : Point)
 (w : PV_OWNO_PointStores.Write) :
 (step combine p w).val = PV_OWNO_PointStores.store combine p.val w := by
 cases w <;> rfl

theorem fold_view (combine : U64 → U32 → U64)
 (writes : List PV_OWNO_PointStores.Write) (p : Point) :
 (writes.foldl (step combine) p).val =
 writes.foldl (PV_OWNO_PointStores.store combine) p.val := by
 induction writes generalizing p with
 | nil => rfl
 | cons w ws ih =>
  rw [List.foldl_cons,List.foldl_cons,ih,step_view]

theorem run_view (combine : U64 → U32 → U64)
 (writes : List PV_OWNO_PointStores.Write) :
 (run combine writes).val = PV_OWNO_PointStores.run combine writes :=
 fold_view combine writes initial

theorem run_canonical (combine : U64 → U32 → U64)
 (writes : List PV_OWNO_PointStores.Write) :
 ∀ q ∈ (run combine writes).val, Canon q := by
 rw [run_view]
 exact PV_OWNO_PointStores.run_canonical combine writes

#print axioms index_bound
#print axioms store_view
#print axioms step_view
#print axioms fold_view
#print axioms run_view
#print axioms run_canonical
end R1Z.PV_OWNP_PointArray
