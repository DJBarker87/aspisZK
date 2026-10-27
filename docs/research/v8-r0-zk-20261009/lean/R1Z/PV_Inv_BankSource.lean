import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_BankSource
open R0P
variable {K : Type} [Field K]

/-- Bounded structural reference for pair_forest_trace.rs:491–519,601–614.
The installed caller must identify its raw descriptors and bank cells with these
objects. Bounds/canonicality are separate P obligations, never hidden here. -/
inductive Bank where | stable | late
  deriving DecidableEq
structure Banks (K : Type) where
  stable : Fin 16 → Fin 1024 → K
  late : Fin 16 → Fin 1024 → K
inductive Limb (K : Type) where
  | zero
  | cell (bank : Bank) (column : Fin 16) (row : Fin 1024) (offset : K)
structure Tuple (K : Type) where
  row : Fin 1024
  limbs : Fin 16 → Limb K

def bankAt (row : Fin 1024) : Bank :=
  if 544 ≤ row.val ∧ row.val < 864 then .late else .stable

def read (banks : Banks K) : Limb K → K
  | .zero => 0
  | .cell .stable col row offset => banks.stable col row + offset
  | .cell .late col row offset => banks.late col row + offset

def value (banks : Banks K) (tuple : Tuple K) : Fin 16 → K :=
  fun i => read banks (tuple.limbs i)

def merged (banks : Banks K) (col : Fin 16) (row : Fin 1024) : K :=
  if 544 ≤ row.val ∧ row.val < 864 then banks.late col row else banks.stable col row

theorem cell_read (banks : Banks K) (col : Fin 16) (row : Fin 1024) (offset : K) :
    read banks (.cell (bankAt row) col row offset) = merged banks col row + offset := by
  unfold bankAt merged
  split <;> rfl

theorem zero_read (banks : Banks K) : read banks .zero = 0 := rfl

#print axioms cell_read
#print axioms zero_read
end R1Z.PV_Inv_BankSource
