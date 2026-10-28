import PV_L2C_M31
set_option autoImplicit false
namespace PV_L2C_PackedMasks

def insert (s : BitVec 16) (p : Fin 16) : BitVec 16 := s ||| ((1 : BitVec 16) <<< p.val)

theorem inserted_bit (s : BitVec 16) (p q : Fin 16) :
    (insert s p).getLsbD q.val=(s.getLsbD q.val || decide (p=q)) := by
  unfold insert
  rw [BitVec.getLsbD_or,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_one]
  simp only [q.isLt,decide_true,Bool.true_and]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,Bool.not_eq_true,decide_eq_true_eq,decide_eq_false_iff_not,Fin.ext_iff]
  omega
#print axioms inserted_bit

abbrev Masks := Fin 64 → BitVec 16

def block (p : Fin 1024) : Fin 64 := ⟨p.val/16,by have := p.isLt;omega⟩
def bit (p : Fin 1024) : Fin 16 := ⟨p.val%16,by omega⟩
def contains (m : Masks) (q : Fin 1024) : Bool := (m (block q)).getLsbD (bit q).val

def put (m : Masks) (p : Fin 1024) : Masks :=
  fun b => if b=block p then insert (m b) (bit p) else m b

theorem put_contains (m : Masks) (p q : Fin 1024) :
    contains (put m p) q=(contains m q || decide (p=q)) := by
  by_cases hb : block q=block p
  · simp only [contains,put,hb,if_pos,inserted_bit]
    have he : (bit p=bit q)↔p=q := by
      have hv := congrArg Fin.val hb
      simp only [block] at hv
      simp only [bit,Fin.ext_iff]
      omega
    rw [he]
  · have hpq : p≠q := by intro h;subst p;exact hb rfl
    simp only [contains,put,hb,if_neg,hpq,decide_false,Bool.or_false]
#print axioms put_contains

def pack (rows : List (Fin 1024)) (m : Masks) : Masks := rows.foldl put m

theorem packed_contains (rows : List (Fin 1024)) (m : Masks) (q : Fin 1024) :
    contains (pack rows m) q=(contains m q || decide (q∈rows)) := by
  induction rows generalizing m with
  | nil => simp only [pack,List.foldl_nil,List.not_mem_nil,decide_false,Bool.or_false]
  | cons p rows ih =>
    change contains (pack rows (put m p)) q=_
    rw [ih,put_contains]
    simp [List.mem_cons,eq_comm,Bool.or_assoc]
#print axioms packed_contains
end PV_L2C_PackedMasks
