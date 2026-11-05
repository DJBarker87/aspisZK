import NFS_AccumPart00
set_option autoImplicit false
noncomputable section
namespace NHH_Embedding
open Aeneas Aeneas.Std Result
open NEV_CodeFieldRaw.aspis_core.field
abbrev reduced := AspisS1M31Embedding.Total.reduce

theorem base (x : U32) :
 M31.Insts.Aspis_coreR0ScalarCodeField.from_m31 x=ok (reduced x) := by
 simp only [M31.Insts.Aspis_coreR0ScalarCodeField.from_m31,NFS_NEV_CodeFieldBridge.rem,bind_tc_ok]

theorem inherent (x : U32) : CM31.from_m31 x=ok ⟨x,0#u32⟩ := by
 simp only [CM31.from_m31,M31.ZERO]

theorem complex (x : U32) :
 CM31.Insts.Aspis_coreR0ScalarCodeField.from_m31 x=ok ⟨reduced x,0#u32⟩ := by
 simp only [CM31.Insts.Aspis_coreR0ScalarCodeField.from_m31,base,inherent,bind_tc_ok]

theorem quadratic (x : U32) :
 QM31.Insts.Aspis_coreR0ScalarCodeField.from_m31 x=
 ok ⟨⟨reduced x,0#u32⟩,⟨0#u32,0#u32⟩⟩ := by
 simp only [QM31.Insts.Aspis_coreR0ScalarCodeField.from_m31,complex,QM31.from_cm31,CM31.ZERO,bind_tc_ok]

theorem wide (x : U32) :
 wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 x=
 ok (NFS_NEV_CodeFieldBridge.value x) := NFS_NEV_CodeFieldBridge.total x

theorem word_spec (x : U32) : (reduced x).val=x.val%2147483647 :=
 AspisS1M31Embedding.Total.reduce_val x

theorem canonical (x : U32) : (reduced x).val<2147483647 := by
 rw [word_spec];exact Nat.mod_lt _ (by omega)

/-- Actual canonical caller coordinate; no independently chosen child success. -/
theorem same_canonical_word (x : U32) (hx : x.val<2147483647) : reduced x=x := by
 apply UScalar.eq_of_val_eq
 rw [word_spec,Nat.mod_eq_of_lt hx]

/-- Existing source callback association, reused on the SAME raw word. -/
theorem accumulation (ops : AspisR1.Port3_NativeQueryBody.Ops) (x : U32)
 (hx : x.val<2147483647) :
 (do let out ← wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 x
     ok (NFS_NEV_CodeFieldBridge.toStage out))=(NBF_RowInstall.install ops).op10 x :=
 NFS_NEV_CodeFieldBridge.cohort ops x hx

#print axioms base
#print axioms inherent
#print axioms complex
#print axioms quadratic
#print axioms wide
#print axioms word_spec
#print axioms canonical
#print axioms same_canonical_word
#print axioms accumulation
end NHH_Embedding
end
