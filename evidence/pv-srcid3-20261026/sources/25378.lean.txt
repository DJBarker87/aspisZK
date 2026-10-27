import R1Z.PV_Src_PathIndex

/-! The native membership index carries precisely the canonical witness's
20 membership direction bits. No finite input space is enumerated. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_PathBits
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open PV_Src_CheckedEncoding

theorem bool_word (b : Bool) : core.convert.num.FromU32Bool.from b =
    (if b then 1#u32 else 0#u32) := by cases b <;> rfl

theorem bit_at (w : W) (n : Nat) (hn : n < 24) :
    (BuilderRecordsPath.bits (PV_Src_NativeDirections.reference
      (nativeWitness w (PV_Src_PathIndex.index w)))).val[n]! =
      if (w.path ⟨n,hn⟩).1 then 1#u32 else 0#u32 := by
  dsimp only [BuilderRecordsPath.bits]
  rw [List.getElem!_eq_getElem?_getD,List.getElem?_ofFn,
    dif_pos (show n < (24#usize : Usize).val by simpa using hn)]
  simp only [Option.getD_some]
  by_cases h0 : n = 0
  · subst n
    rw [if_pos rfl]
    exact bool_word _
  · rw [if_neg h0]
    by_cases h20 : n ≤ 20
    · rw [if_pos h20]
      apply UScalar.eq_of_val_eq
      rw [bit_val _ _ (by simp;omega)]
      have hb := PV_Src_PathIndex.bit w ⟨n-1,by omega⟩
      have he : (⟨(n-1)+1,by omega⟩ : Fin 24) = ⟨n,hn⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
      rw [he] at hb
      change (PV_Src_PathIndex.index w).val / 2^(n-1) % 2 =
        (if (w.path ⟨n,hn⟩).1 then 1#u32 else 0#u32).val
      cases hbit : (w.path ⟨n,hn⟩).1 <;>
        simpa only [hbit,Bool.toNat_false,Bool.toNat_true,Bool.false_eq_true,
          if_false,if_true,UScalar.ofNatCore_val_eq] using hb
    · rw [if_neg h20]
      change core.convert.num.FromU32Bool.from ((arr3 _).val[n-21]!) = _
      rw [arr3_get _ _ (by omega)]
      have he : (⟨(n-21)+21,by omega⟩ : Fin 24) = ⟨n,hn⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
      rw [he,bool_word]

theorem bits (w : W) :
    BuilderRecordsPath.bits (PV_Src_NativeDirections.reference
      (nativeWitness w (PV_Src_PathIndex.index w))) =
      (BuilderCanonical.rustWitness w).bits := by
  apply BuilderRecordCanonical.array_ext
  intro n hn
  have hn' : n < 24 := by simpa using hn
  rw [bit_at w n hn']
  change _ = (R1J.SpendWitnessMap.arr24 _).val[n]!
  rw [R1J.SpendWitnessMap.arr24_get _ n hn']
  rfl

#print axioms bool_word
#print axioms bit_at
#print axioms bits
end R1Z.PV_Src_PathBits
