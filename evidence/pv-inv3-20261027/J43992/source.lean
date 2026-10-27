import R1Z.PV_Inv_BankSource
import R1Z.PV_Inv_EmbedArithmetic
set_option autoImplicit false
namespace R1Z.PV_Inv_RawBankRead
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47 ProverCommitM31Ops48
open ProverCommitScalar48 (embed)
open AspisR1.ExtractedCurrentQM31Exact (QM31Exact)
open PV_Inv_BankSource

def banks (b : Banks U32) : Banks QM31Exact :=
  ⟨fun c r => embed (b.stable c r),fun c r => embed (b.late c r)⟩
def limb : Limb U32 → Limb QM31Exact
  | .zero => .zero
  | .cell bank c r offset => .cell bank c r (embed offset)

def read (b : Banks U32) : Limb U32 → Result U32
  | .zero => ok 0#u32
  | .cell .stable c r offset => field.M31.add (b.stable c r) offset
  | .cell .late c r offset => field.M31.add (b.late c r) offset

def CanonicalBanks (b : Banks U32) : Prop :=
  (∀ c r, canonical (b.stable c r)) ∧ (∀ c r, canonical (b.late c r))
def CanonicalLimb : Limb U32 → Prop
  | .zero => True
  | .cell _ _ _ offset => canonical offset

theorem exact_read (b : Banks U32) (hb : CanonicalBanks b)
    (l : Limb U32) (hl : CanonicalLimb l) :
    ∃ z, read b l = ok z ∧ canonical z ∧ embed z = PV_Inv_BankSource.read (banks b) (limb l) := by
  cases l with
  | zero => exact ⟨0#u32,rfl,by decide,rfl⟩
  | cell bank c r offset =>
    cases bank with
    | stable => exact PV_Inv_EmbedArithmetic.add_source (b.stable c r) offset (hb.1 c r) hl
    | late => exact PV_Inv_EmbedArithmetic.add_source (b.late c r) offset (hb.2 c r) hl

#print axioms exact_read
end R1Z.PV_Inv_RawBankRead
