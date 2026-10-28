import R1Z.PV_RDEA_AppendRequests
import R1Z.PV_RDEA_V178
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_PathSchedule
open PV_RDB1_V183_ReserveWorld PV_RDEA_AppendRequests

structure Header where
  len : Nat
  cap : Nat
  deriving DecidableEq

/-- Header transition on successful append; failure terminates before this
transition. This is not an allocator-success hypothesis. -/
def afterAppend (h : Header) (count : Nat) : Header :=
  ⟨h.len+count,nextCapacity h.len h.cap count⟩

def appendWord (h : Header) (count : Nat) : List (Nat × Nat × Nat) :=
  requests 18446744073709551615 9223372036854775807 h.len h.cap count

/-- Clone-first allocation sizes and order along the returning branch. A real
failure returns a prefix of this word; the failure event belongs to retained
runtime/allocator primitive adequacy (rdea-1), rather than a new trust item. -/
def joinWord (baseLen pathLen : Nat) (absolute needSep : Bool) :
    List (Nat × Nat × Nat) :=
  let cloned : Header := ⟨baseLen,baseLen⟩
  let cleared := if absolute then {cloned with len:=0} else cloned
  let sep := !absolute && needSep
  let sepWord := if sep then appendWord cleared 1 else []
  let afterSep := if sep then afterAppend cleared 1 else cleared
  (if baseLen=0 then [] else [(0,baseLen,1)]) ++ sepWord ++ appendWord afterSep pathLen

theorem public_word (baseLen pathLen baseLen' pathLen' : Nat)
    (absolute needSep absolute' needSep' : Bool)
    (hb : baseLen=baseLen') (hp : pathLen=pathLen')
    (ha : absolute=absolute') (hs : needSep=needSep') :
    joinWord baseLen pathLen absolute needSep=joinWord baseLen' pathLen' absolute' needSep' := by
  rw [hb,hp,ha,hs]

/-- Absolute arguments still clone the base before clearing it. -/
theorem absolute_word (baseLen pathLen : Nat) (needSep : Bool) :
    joinWord baseLen pathLen true needSep =
      (if baseLen=0 then [] else [(0,baseLen,1)]) ++
      appendWord ⟨0,baseLen⟩ pathLen := by
  simp [joinWord]

/-- All five direct application joins use relative literal/hex names. -/
theorem relative_word (baseLen pathLen : Nat) (needSep : Bool) :
    joinWord baseLen pathLen false needSep =
      (if baseLen=0 then [] else [(0,baseLen,1)]) ++
      (if needSep then appendWord ⟨baseLen,baseLen⟩ 1 else []) ++
      appendWord (if needSep then afterAppend ⟨baseLen,baseLen⟩ 1 else
        ⟨baseLen,baseLen⟩) pathLen := by
  simp [joinWord]

/-- Truncating a cloned buffer changes no capacity, request, or address. -/
theorem clear_header (b : Buffer U8) :
    (PV_RDB1_V178.cleared b).capacity=b.capacity ∧
    (PV_RDB1_V178.cleared b).values.length=0 ∧
    (PV_RDB1_V178.cleared b).address=b.address := ⟨rfl,rfl,rfl⟩

/-- Name-length recurrence from 32 digest bytes: two hex digits per byte,
followed by the five-byte suffix. No digest-byte value occurs in this law. -/
def nameLength : Nat → Nat
  | 0 => 5
  | n+1 => 2+nameLength n

theorem name_length (remaining : Nat) : nameLength remaining=2*remaining+5 := by
  induction remaining with
  | zero => rfl
  | succ n ih => simp only [nameLength,ih]; omega

theorem reservation_length : nameLength 32=69 := by
  rw [name_length]

#print axioms public_word
#print axioms absolute_word
#print axioms relative_word
#print axioms clear_header
#print axioms name_length
#print axioms reservation_length
end R1Z.PV_RDEA_PathSchedule
