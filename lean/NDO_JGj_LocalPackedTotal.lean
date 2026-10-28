import NDO_JGj_RawPackedTotal
import RPv_FJe_RawLocalCanon
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_LocalPackedTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
theorem converted (raw : Array U64 4#usize) :
    ∃ out,state_only_poseidon.extension_from_raw_limbs raw=ok out ∧ Canon out := by
  obtain ⟨q,hq,_,_⟩ := RawPoseidonExtensionWords.extension_from_raw_limbs_words raw
  have same := FJb_RawConversion.converted raw
  rw [hq] at same
  cases run : state_only_poseidon.extension_from_raw_limbs raw with
  | fail e => rw [run] at same;cases same
  | div => rw [run] at same;cases same
  | ok out => exact ⟨out,rfl,FJe_RawLocalCanon.converted raw out run⟩
theorem source (input : Array NQ 4#usize) (hc : canonical input) :
    ∃ out,state_only_poseidon.external_local_packed input=ok out ∧ Canon out := by
  obtain ⟨raw,rr⟩ := JGj_RawPackedTotal.source input hc
  obtain ⟨out,ro,co⟩ := converted raw
  refine ⟨out,?_,co⟩
  unfold state_only_poseidon.external_local_packed
  rw [rr,bind_tc_ok,ro]
#print axioms converted
#print axioms source
end AspisR1.JGj_LocalPackedTotal
end
