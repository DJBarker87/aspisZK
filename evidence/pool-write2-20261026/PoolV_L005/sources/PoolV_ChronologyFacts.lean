import PoolV_ChronologyExact
set_option autoImplicit false
namespace AspisR1.PoolV_ChronologyFacts
open Aeneas Aeneas.Std Result

def decreased (new old : Slice U64) : Bool :=
  (new.val.zip old.val).any (fun x => decide (x.1 < x.2))
def progressed (new old : Slice U64) : Bool :=
  (new.val.zip old.val).any (fun x => decide (x.1 > x.2))

def specification (new old : Slice U64) (has : Bool) (sequence : U64) : U8 × U64 :=
  if has && decreased new old then (1#u8,0#u64)
  else if has && !progressed new old then (2#u8,0#u64)
  else if sequence = core.num.U64.MAX then (3#u8,0#u64)
  else (0#u8,U64.wrapping_add sequence 1#u64)

theorem total (new old : Slice U64) (has : Bool) (sequence : U64) :
    PoolV_Chronology.chronology new old has sequence = ok (specification new old has sequence) := by
  unfold PoolV_Chronology.chronology
  rw [PoolV_ChronologyExact.exact]
  cases has <;> cases hd : decreased new old <;> cases hp : progressed new old <;>
    simp_all [specification,decreased,progressed,lift]

theorem accepted (new old : Slice U64) (has : Bool) (sequence next : U64) :
    PoolV_Chronology.chronology new old has sequence = ok (0#u8,next) ↔
      (has = true → decreased new old = false ∧ progressed new old = true) ∧
      sequence ≠ core.num.U64.MAX ∧ next = U64.wrapping_add sequence 1#u64 := by
  rw [total]
  cases has <;> cases hd : decreased new old <;> cases hp : progressed new old <;>
    by_cases hs : sequence = core.num.U64.MAX <;>
    simp [specification,hd,hp,hs,eq_comm]

#print axioms total
#print axioms accepted
end AspisR1.PoolV_ChronologyFacts
