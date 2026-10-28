import PV_L2C_HashTotal
import PV_L2C_DigestOrigin
import R1Z.BuilderAdmissionCanonical
set_option autoImplicit false
namespace PV_L2C_PlannerOutputs
open Aeneas Aeneas.Std Result R1Z R0Z.WriterRefine BuilderForestAdmissionPort
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary

/-- Release-width seed arithmetic followed by the planner's final `% P`.
All bounds below hold even when the seed additions wrap. -/
def prior (seed : U32) (j : Fin 8) : U32 :=
  ⟨seed.bv + BitVec.ofNat 32 17 * BitVec.ofNat 32 j.val + BitVec.ofNat 32 1⟩
def generated (seed : U32) : Array U32 8#usize :=
  arr8 (fun j => PV_L2C_GeneratedRange.remainder (prior seed j))

theorem generated_origin (seed : U32) : PV_L2C_DigestOrigin.Origin (generated seed) := by
  apply PV_L2C_DigestOrigin.Origin.generated (prior seed)
  intro j
  exact arr8_get _ j.val j.isLt
#print axioms generated_origin

theorem generated_range (seed : U32) : Canon8 (generated seed) :=
  PV_L2C_DigestOrigin.canonical _ (generated_origin seed)
#print axioms generated_range

/-- Source wrapper cut of derive_owner_key: owner domain and exactly the
eight generated key words. Native wrapper binding is recorded separately. -/
def owner (seed : U32) : Result (Array U32 8#usize) :=
  poseidon2.hash_fields 1095958529#u32 (Array.to_slice (generated seed))

theorem owner_total (seed : U32) :
    ∃ key, owner seed = ok key ∧ PV_L2C_DigestOrigin.Origin key := by
  have len : (Array.to_slice (generated seed)).val.length = 8 := by
    simpa only [Array.to_slice,UScalar.ofNatCore_val_eq] using (generated seed).property
  have hx : ∀ x ∈ (Array.to_slice (generated seed)).val, x.val < 2147483647 :=
    (BuilderAdmissionCanonical.canon_iff_list _).mp (generated_range seed)
  have nonempty : (Array.to_slice (generated seed)).val ≠ [] := by
    intro he;rw [he] at len;cases len
  obtain ⟨key,hkey,_⟩ := PV_L2C_HashTotal.source 1095958529#u32
    (Array.to_slice (generated seed)) (by scalar_tac) (by rw [len];omega) nonempty hx
  exact ⟨key,hkey,.hashed 1095958529#u32 _ (by scalar_tac) (by rw [len];omega) nonempty hkey⟩
#print axioms owner_total

theorem outputs (n : U32) :
    ∃ recipient change,
      owner 300#u32 = ok recipient ∧
      owner (U32.wrapping_add 500#u32 n) = ok change ∧
      PV_L2C_DigestOrigin.Origin recipient ∧ PV_L2C_DigestOrigin.Origin change ∧
      PV_L2C_DigestOrigin.Origin (generated 400#u32) ∧
      PV_L2C_DigestOrigin.Origin (generated (U32.wrapping_add 600#u32 n)) := by
  obtain ⟨recipient,hr,hor⟩ := owner_total 300#u32
  obtain ⟨change,hc,hoc⟩ := owner_total (U32.wrapping_add 500#u32 n)
  exact ⟨recipient,change,hr,hc,hor,hoc,generated_origin _,generated_origin _⟩
#print axioms outputs
end PV_L2C_PlannerOutputs
