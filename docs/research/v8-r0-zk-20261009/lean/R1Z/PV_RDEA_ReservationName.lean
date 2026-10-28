import R1Z.PV_RDEA_PathSchedule
namespace R1Z.PV_RDEA_ReservationName

/-- ASCII digit table expressed by its two contiguous ranges. -/
def digit (n : Fin 16) : Nat := if n.val<10 then 48+n.val else 87+n.val

theorem digit_not_slash (n : Fin 16) : digit n≠47 := by
  unfold digit
  split <;> omega

def high (b : Fin 256) : Fin 16 := ⟨b.val/16,by omega⟩
def low (b : Fin 256) : Fin 16 := ⟨b.val%16,Nat.mod_lt _ (by omega)⟩

/-- Byte-level owned reference for the two push_str calls per digest byte. -/
def hex : List (Fin 256) → List Nat
  | [] => []
  | b::rest => digit (high b)::digit (low b)::hex rest

def suffix : List Nat := [46,98,117,114,110]
def name (digest : List (Fin 256)) : List Nat := hex digest ++ suffix

theorem hex_length (digest : List (Fin 256)) : (hex digest).length=2*digest.length := by
  induction digest with
  | nil => rfl
  | cons b bs ih => simp only [hex,List.length_cons,ih]; omega

theorem name_length (digest : List (Fin 256)) :
    (name digest).length=2*digest.length+5 := by
  simp only [name,List.length_append,hex_length,suffix,List.length_cons,List.length_nil]

theorem hex_no_slash (digest : List (Fin 256)) : 47 ∉ hex digest := by
  induction digest with
  | nil => simp only [hex,List.not_mem_nil,not_false_eq_true]
  | cons b bs ih =>
    simp only [hex,List.mem_cons,not_or]
    exact ⟨Ne.symm (digit_not_slash _),Ne.symm (digit_not_slash _),ih⟩

theorem name_no_slash (digest : List (Fin 256)) : 47 ∉ name digest := by
  simp only [name,List.mem_append,not_or]
  refine ⟨hex_no_slash digest,?_⟩
  simp [suffix]

theorem fixed_name_length (digest : List (Fin 256)) (size : digest.length=32) :
    (name digest).length=69 := by
  rw [name_length,size]

/-- A digest byte can change the basename, but neither the join's absolute-path
branch nor any request size. No public-digest-content premise is necessary. -/
theorem schedule_independent (digest1 digest2 : List (Fin 256))
    (s1 : digest1.length=32) (s2 : digest2.length=32)
    (baseLen : Nat) (needSep : Bool) :
    PV_RDEA_PathSchedule.joinWord baseLen (name digest1).length false needSep =
      PV_RDEA_PathSchedule.joinWord baseLen (name digest2).length false needSep := by
  rw [fixed_name_length digest1 s1,fixed_name_length digest2 s2]

#print axioms digit_not_slash
#print axioms hex_length
#print axioms name_length
#print axioms hex_no_slash
#print axioms name_no_slash
#print axioms fixed_name_length
#print axioms schedule_independent
end R1Z.PV_RDEA_ReservationName
