import PV_B3P_DigestRegions226V3
import PV_B3P_FrontierTotal226V3
namespace PV_B3P_ByteTotal226V3
open Aeneas Aeneas.Std PV_B3P_226V3
set_option autoImplicit false

structure Canonical (p : reference226.OwnedPublic) : Prop where
  anchor : ∀ m ∈ p.anchor.val, m < 2147483647#u32
  nullifier : ∀ m ∈ p.nullifier.val, m < 2147483647#u32
  asset : p.asset_id < 2147483647#u32
  recipient : ∀ m ∈ p.recipient.val, m < 2147483647#u32
  change : ∀ m ∈ p.change.val, m < 2147483647#u32
  amount : p.withdrawal_amount < 2147483647#u32
  frontier : ∀ row ∈ p.frontier.val, ∀ m ∈ row.val, m < 2147483647#u32
  root : ∀ m ∈ p.next_root.val, m < 2147483647#u32
  next_frontier : ∀ row ∈ p.next_frontier.val, ∀ m ∈ row.val, m < 2147483647#u32

theorem field_total (v : U32) (j : Usize) (h : v < 2147483647#u32) :
    ∃ b, reference226.field_byte v j = .ok (.Ok b) :=
  ⟨_,PV_B3P_ByteScalar226V3.field_success v j h⟩

theorem success (p : reference226.OwnedPublic) (i : Usize) (hc : Canonical p) :
    ∃ v, reference226.byte_at p i = .ok (.Ok v) := by
  obtain ⟨ha,hn,hs,hr,hc,hm,hf,hroot,hnf⟩ := hc
  have c0 : Usize.wrapping_add 70#usize 32#usize = 102#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  have c1 : Usize.wrapping_add 102#usize 32#usize = 134#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  have c2 : Usize.wrapping_add 70#usize 33#usize = 103#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  have c3 : Usize.wrapping_add 102#usize 33#usize = 135#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  have c4 : Usize.wrapping_add 107#usize 8#usize = 115#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  have c5 : Usize.wrapping_add 135#usize 8#usize = 143#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  have c6 : Usize.wrapping_add 115#usize 640#usize = 755#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  have c7 : Usize.wrapping_add 143#usize 640#usize = 783#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  have c8 : Usize.wrapping_add 115#usize 672#usize = 787#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  have c9 : Usize.wrapping_add 143#usize 672#usize = 815#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  unfold reference226.byte_at
  cases hp : p.withdrawal <;>
    simp only [hp,Bool.false_eq_true,↓reduceIte,lift,bind_tc_ok,
      c0,c1,c2,c3,c4,c5,c6,c7,c8,c9]
  all_goals split_ifs
  all_goals first
    | exact ⟨_,rfl⟩
    | apply field_total <;> assumption
    | apply PV_B3P_DigestTotal226V3.success
      · repeat rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
        scalar_tac
      · assumption
    | apply PV_B3P_FrontierTotal226V3.success
      · repeat rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
        scalar_tac
      · assumption
    | exfalso; scalar_tac

#print axioms field_total
#print axioms success
end PV_B3P_ByteTotal226V3
