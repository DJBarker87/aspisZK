import R1Z.CouplingR1PBin
import Mathlib.Data.List.OfFn

/-! A classical finite byte-string ROM. No concrete address space or table
is enumerated by the kernel. The address bound is a model parameter. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.RomFiniteBin
open R0Z.FsStatement R1Z.GamesR1 R1Z.CouplingR1PBin
attribute [local instance] Classical.propDecidable

/-- All strings of at most `bound` bytes, via finite vectors. -/
def domain (bound : ℕ) : Finset (List UInt8) :=
  Finset.univ.image (fun p : (Σ n : Fin (bound + 1), Fin n.val → UInt8) => List.ofFn p.2)

theorem mem_domain (bound : ℕ) (bs : List UInt8) :
    bs ∈ domain bound ↔ bs.length ≤ bound := by
  constructor
  · intro hb
    obtain ⟨⟨n, v⟩, _, rfl⟩ := Finset.mem_image.mp hb
    simpa only [List.length_ofFn] using Nat.le_of_lt_succ n.isLt
  · intro hb
    exact Finset.mem_image.mpr ⟨⟨⟨bs.length, Nat.lt_succ_of_le hb⟩, bs.get⟩,
      Finset.mem_univ _, List.ofFn_get bs⟩

abbrev Address (bound : ℕ) := {bs : List UInt8 // bs ∈ domain bound}

instance address_nonempty (bound : ℕ) : Nonempty (Address bound) :=
  ⟨⟨[], (mem_domain bound []).mpr (Nat.zero_le _)⟩⟩

def decode (bound : ℕ) (bs : List UInt8) : Option (Address bound) :=
  if hb : bs ∈ domain bound then some ⟨bs, hb⟩ else none

theorem decode_encode (bound : ℕ) (a : Address bound) : decode bound a.val = some a := by
  simp only [decode, dif_pos a.property]

theorem encode_decode (bound : ℕ) (bs : List UInt8) (a : Address bound)
    (ha : decode bound bs = some a) : a.val = bs := by
  unfold decode at ha
  split at ha
  · cases Option.some.inj ha
    rfl
  · contradiction

theorem decode_isSome (bound : ℕ) (bs : List UInt8) :
    (decode bound bs).isSome ↔ bs.length ≤ bound := by
  by_cases hb : bs ∈ domain bound
  · simp only [decode, dif_pos hb, Option.isSome_some, Bool.true_eq, true_iff]
    exact (mem_domain bound bs).mp hb
  · simp only [decode, dif_neg hb, Option.isSome_none, Bool.false_eq_true, false_iff]
    exact fun hl => hb ((mem_domain bound bs).mpr hl)

def lookup (bound : ℕ) (tab : Address bound → OracleAnswer) (bs : List UInt8) : OracleAnswer :=
  match decode bound bs with
  | some a => tab a
  | none => 0

variable {K CommitHandle Aux : Type} [Field K]

/-- Choose the table model and the claimed adversary class. All protocol
encodings/decoders are retained from `base`; its old table and cap are unused. -/
def wire (base : R1Wire K CommitHandle Aux) (bound : ℕ) : R1Wire K CommitHandle Aux :=
  { base with
    Tab := Address bound → OracleAnswer
    finTab := inferInstance
    neTab := inferInstance
    look := lookup bound
    qmax := 2^64 }

variable [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K]

def rom (base : R1Wire K CommitHandle Aux) (bound : ℕ) : RomModel (wire base bound) where
  A := Address bound
  finA := inferInstance
  deqA := inferInstance
  neA := inferInstance
  dec := decode bound
  enc := Subtype.val
  dec_enc := decode_encode bound
  enc_of_dec := encode_decode bound
  eTab := Equiv.refl _
  look_eq := by
    intro tab bs
    change lookup bound tab bs = _
    unfold lookup
    cases decode bound bs <;> rfl

theorem lookup_law (base : R1Wire K CommitHandle Aux) (bound : ℕ)
    (tab : (wire base bound).Tab) (a : Address bound) :
    (wire base bound).look tab a.val = tab a := by
  change lookup bound tab a.val = tab a
  unfold lookup
  rw [decode_encode]

theorem adversary_budget (base : R1Wire K CommitHandle Aux) (bound : ℕ) :
    (wire base bound).qmax ≤ 2^64 := Nat.le_refl _

/-- Uniform tables are transported by the full table equivalence. -/
theorem table_uniform (base : R1Wire K CommitHandle Aux) (bound : ℕ) :
    MP (rom base bound).eTab := mp_equiv _

#print axioms mem_domain
#print axioms decode_encode
#print axioms encode_decode
#print axioms decode_isSome
#print axioms rom
#print axioms lookup_law
#print axioms adversary_budget
#print axioms table_uniform
end R1Z.RomFiniteBin
