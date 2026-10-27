import FIx_ScheduleIndices
import FIx_ArrayMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_InitialWrites
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K)
abbrev I := Fin (16#usize).val

theorem rate_fin : (⟨poseidon2.RATE.val,FIx_ScheduleIndices.rate_bound⟩ : I)=⟨8,by decide⟩ := by
  apply Fin.ext
  change poseidon2.RATE.val=8
  simp only [poseidon2.RATE]
  rfl

theorem nine_fin (i : Usize) (vi : i.val=9) :
    (⟨i.val,FIx_ScheduleIndices.nine_bound i vi⟩ : I)=⟨9,by decide⟩ := Fin.ext vi

theorem rate_ne_nine : (⟨9,by decide⟩ : I)≠⟨8,by decide⟩ := by
  intro h
  have he := congrArg Fin.val h
  norm_num only at he

theorem value (raw : I → K) (selector domain length : K) :
    Function.update (Function.update raw ⟨8,by decide⟩ (raw ⟨8,by decide⟩-selector*domain))
      ⟨9,by decide⟩ ((Function.update raw ⟨8,by decide⟩ (raw ⟨8,by decide⟩-selector*domain))
        ⟨9,by decide⟩-selector*length)=
    Function.update (Function.update raw ⟨8,by decide⟩ (raw ⟨8,by decide⟩-selector*domain))
      ⟨9,by decide⟩ (raw ⟨9,by decide⟩-selector*length) := by
  rw [Function.update_of_ne rate_ne_nine]
#print axioms rate_fin
#print axioms nine_fin
#print axioms rate_ne_nine
#print axioms value
end AspisR1.FIx_InitialWrites
end
