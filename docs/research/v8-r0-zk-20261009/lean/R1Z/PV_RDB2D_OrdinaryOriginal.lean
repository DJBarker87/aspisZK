import R1Z.PV_RDB2D_SamplerCore
import R1Z.PV_RDB2D_ProverRwFullTypes
set_option autoImplicit false
namespace PV_B2_E_OrdinaryOriginal
open Aeneas Aeneas.Std Result
open PV_B2_C_ArrayDigits
abbrev Bytes := Array U8 32#usize
abbrev Digits := Array U32 8#usize
abbrev Raw := PV_B2_C_249.aspis_core.field.wide_exact.WideExact
abbrev Native := ProverRwFull.aspis_core.field.wide_exact.WideExact

/-- The original WideExact::new reduces each raw limb modulo P. -/
def reduce (x : U32) : U32 := UScalar.ofNatCore (x.val % 2147483647)
  (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
def decode (a : Digits) : Raw :=
  ⟨⟨⟨reduce (limb a 0),reduce (limb a 1)⟩,⟨reduce (limb a 2),reduce (limb a 3)⟩⟩,
   ⟨⟨reduce (limb a 4),reduce (limb a 5)⟩,⟨reduce (limb a 6),reduce (limb a 7)⟩⟩⟩

/-- Structural representation of frozen ordinary_sample: eight ordered divisions,
then the original reducing decoder. See ORDINARY-STRUCTURAL-BINDING.json.
This is not the unfaithful mutable-iterator Aeneas emission. -/
def original (b : Bytes) : Result Raw := do
  let (digits,_) ← PV_B2_C_OrdinaryReference.sampler_owned.low_base_p_digits b
  ok (decode digits)

theorem reduce_eq (x : U32) (h : x.val < 2147483647) : reduce x = x := by
  apply UScalar.eq_of_val_eq
  simp only [reduce,UScalar.ofNatCore_val_eq,Nat.mod_eq_of_lt h]

theorem decode_eq (a : Digits) (h : canonical a) : decode a = raw a := by
  simp only [decode,raw,reduce_eq _ (h _)]

theorem digits_canonical (b : Bytes) (a : Digits)
    (hv : AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge.values a =
      AspisR1.SamplerNatModel.ordinaryDigits (AspisR1.SourceSamplerByteRank.rank b)) :
    canonical a := by
  intro i
  have hm : (limb a i).val ∈ AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge.values a := by
    change (limb a i).val ∈ a.val.map UScalar.val
    exact List.mem_map.mpr ⟨_,List.getElem_mem (by rw [a.property];exact i.isLt),rfl⟩
  rw [hv] at hm
  exact PV_B2_C_ordinary_sample.low_canonical _ 8 _ AspisR1.SamplerMachineBounds.P_pos _ hm

/-- All input blocks, complete Result, without a success or canonicality premise. -/
theorem copy_equal_original (b : Bytes) :
    PV_B2_C_Sampler.host_sampler.ordinary_sample b = original b := by
  obtain ⟨a,q,hl,hv,_⟩ := PV_B2_C_RankDigits.source b
  have hc := digits_canonical b a hv
  unfold PV_B2_C_Sampler.host_sampler.ordinary_sample original
  rw [← PV_B2_C_LowDigits.source b,hl]
  simp only [bind_tc_ok]
  change PV_B2_C_Sampler.host_sampler.decode8 a = ok (decode a)
  rw [decode_eq a hc]
  exact PV_B2_C_ArrayDigits.decode a hc

def toNative (v : Raw) : Native :=
  ⟨⟨⟨v.c0.c0.a,v.c0.c0.b⟩,⟨v.c0.c1.a,v.c0.c1.b⟩⟩,
   ⟨⟨v.c1.c0.a,v.c1.c0.b⟩,⟨v.c1.c1.a,v.c1.c1.b⟩⟩⟩
def fromNative (v : Native) : Raw :=
  ⟨⟨⟨v.c0.c0.a,v.c0.c0.b⟩,⟨v.c0.c1.a,v.c0.c1.b⟩⟩,
   ⟨⟨v.c1.c0.a,v.c1.c0.b⟩,⟨v.c1.c1.a,v.c1.c1.b⟩⟩⟩
def mapResult {α β : Type} (f : α → β) : Result α → Result β
  | .ok v => .ok (f v)
  | .fail e => .fail e
  | .div => .div
@[simp] theorem roundtrip (x : Raw) : fromNative (toNative x) = x := by cases x; rfl
@[simp] theorem roundtrip_native (x : Native) : toNative (fromNative x) = x := by cases x; rfl

theorem native_result (b : Bytes) :
    ∃ a : Digits,
      mapResult toNative (PV_B2_C_Sampler.host_sampler.ordinary_sample b) =
        ok (toNative (raw a)) ∧
      AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge.values a =
        AspisR1.SamplerNatModel.ordinaryDigits (AspisR1.SourceSamplerByteRank.rank b) := by
  obtain ⟨a,he,hv⟩ := PV_B2_C_ordinary_sample.op250_source b
  exact ⟨a,by rw [he];rfl,hv⟩
#print axioms reduce
#print axioms decode
#print axioms original
#print axioms reduce_eq
#print axioms decode_eq
#print axioms digits_canonical
#print axioms copy_equal_original
#print axioms roundtrip
#print axioms roundtrip_native
#print axioms native_result
end PV_B2_E_OrdinaryOriginal
