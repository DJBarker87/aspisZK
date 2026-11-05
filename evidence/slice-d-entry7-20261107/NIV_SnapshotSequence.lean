import NIM_NHY_SnapshotJoin
import NIS_AdmissionSdk
import NIS_SnapshotAbi
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIV_SnapshotSequence
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Consolidation
abbrev Spec := Nat × Usize × Usize

def value (e : Entry) (s : Spec) : Owned := e.snapshot s.1 s.2.1.val s.2.2.val

/-- Complete SDK read/drop history and returned OwnedAccount, using the SAME
entry and selected account. The record equation is the existing CLOSED
snapshot law; this is not the missing native wrapper ABI certificate. -/
def Produced {W : Type} (L : Library W (Nat → Record)) (e : Entry)
    (w next : W) (s : Spec) (record : Owned) : Prop :=
  ∃ token owner entered viewed,
    L.run w (.shared s.1 token owner) = (entered,.guard token) ∧
    L.run entered (.deref token) =
      (viewed,.payload (e.heap.payload (e.heap.accounts s.1).1)) ∧
    L.run viewed (.drop token) = (next,.unit) ∧
    (let old := (e.records (e.handles s.1).1).owned
     (do let returned ← NHJ_SnapshotReference.snapshot_ref old.key old.owner
           old.is_signer old.is_writable old.executable s.2.1 s.2.2
           (.Ok (e.buffers (e.handles s.1).1))
         ok (NHJ_SnapshotAssociation.port returned)) = ok record)

inductive Sequence {W : Type} (L : Library W (Nat → Record)) (e : Entry) :
    W → List Spec → List Owned → W → Prop
  | nil (w : W) : Sequence L e w [] [] w
  | cons {w middle final : W} {s : Spec} {ss : List Spec} {r : Owned} {rs : List Owned} :
      Produced L e w middle s r → Sequence L e middle ss rs final →
      Sequence L e w (s::ss) (r::rs) final

theorem one {W : Type} (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (e : Entry) (w : W) (related : L.related w e.heap) (valid : Valid e.heap) (s : Spec) :
    ∃ next, Produced L e w next s (value e s) ∧ L.related next e.heap := by
  obtain ⟨token,owner,entered,viewed,next,acquired,dereferenced,dropped,restored,record⟩ :=
    NHY_SnapshotJoin.source e L sdk w related valid s.1 s.2.1 s.2.2
  exact ⟨next,⟨token,owner,entered,viewed,acquired,dereferenced,dropped,record⟩,restored⟩

/-- No independence or distinct-handle premise: the complete record producer
restores relatedness to the same heap before each subsequent account. -/
theorem sequence {W : Type} (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (e : Entry) (valid : Valid e.heap) (ss : List Spec) (w : W)
    (related : L.related w e.heap) :
    ∃ next, Sequence L e w ss (ss.map (value e)) next ∧ L.related next e.heap := by
  induction ss generalizing w with
  | nil => exact ⟨w,.nil w,related⟩
  | cons s ss ih =>
    obtain ⟨middle,produced,restored⟩ := one L sdk e w related valid s
    obtain ⟨final,remaining,restoredFinal⟩ := ih middle restored
    exact ⟨final,.cons produced remaining,restoredFinal⟩

def firstSpecs : List Spec :=
  [(0,58295#usize,58295#usize),(1,1880#usize,1880#usize),(2,1768#usize,1768#usize)]
def secondSpecs : List Spec :=
  [(0,58295#usize,58295#usize),(1,384#usize,384#usize),(2,192#usize,192#usize),
   (3,768#usize,768#usize),(4,128#usize,256#usize),(5,192#usize,320#usize),
   (6,1768#usize,1768#usize)]

theorem first_records (e : Entry) : firstSpecs.map (value e) = e.first.val := rfl
theorem second_records (e : Entry) :
    secondSpecs.map (value e) = (e.second S2W_D189Wrappers.secondSizes).val := rfl

/-- Applies admission1, including its SAME entry/world, to the complete three
producer results. Native ABI and allocator realization remain separate. -/
theorem first {W : Type} (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (e : Entry) (w : W) (admission : RuntimeEntrypointAdmission L e w 3) :
    ∃ next, Sequence L e w firstSpecs e.first.val next ∧ L.related next e.heap := by
  rw [← first_records]
  exact sequence L sdk e admission.entry.valid firstSpecs w admission.related

theorem second {W : Type} (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (e : Entry) (w : W) (admission : RuntimeEntrypointAdmission L e w 7) :
    ∃ next, Sequence L e w secondSpecs (e.second S2W_D189Wrappers.secondSizes).val next ∧
      L.related next e.heap := by
  rw [← second_records]
  exact sequence L sdk e admission.entry.valid secondSpecs w admission.related

/-- Snapshot production and release return to the same heap before the
exclusive checkpoint operation is applied under admission1. -/
theorem first_then_exclusive {W : Type} (L : Library W (Nat → Record))
    (sdk : S2TrustedSdkBorrow L) (e : Entry) (w : W)
    (admission : RuntimeEntrypointAdmission L e w 3) :
    ∃ next, Sequence L e w firstSpecs e.first.val next ∧
      Matches L next (.exclusive 2 0 0)
        (acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive,.guard 0) := by
  obtain ⟨next,produced,related⟩ := first L sdk e w admission
  exact ⟨next,produced,NIS_AdmissionSdk.exclusive L sdk e next 3 2 0 0
    ⟨admission.entry,related⟩ (by omega)⟩

#print axioms one
#print axioms sequence
#print axioms first_records
#print axioms second_records
#print axioms first
#print axioms second
#print axioms first_then_exclusive
end AspisR1.NIV_SnapshotSequence
