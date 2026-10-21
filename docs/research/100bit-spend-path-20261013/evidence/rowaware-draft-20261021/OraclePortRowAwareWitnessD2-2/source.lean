import OraclePortRowAwareCausalD1
import OracleDecisionMultiDecoder

/-! Finite, fully cached row-zero history for the frozen node overlap.
Unlike the older witness, this table has no leaf answer equal to iv. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortRowAwareWitnessD2
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open CanonicalAddressEmbedding OracleDecisionMultiDecoder
open OraclePortRowAwareCausalD1

def squeezed : Bytes := (squeezeA p absorbed).toBytes
def answer : State := fun _ => 5

def support : Table Bytes State := fun b =>
  if b = initial.toBytes then some s0 else
  if b = row0.toBytes then some absorbed else
  if b = advanced.toBytes then some endpoint else
  if b = squeezed then some answer else none

theorem support_fibers :
    (∀ b, support b = some s0 ↔ b = initial.toBytes) ∧
    (∀ b, support b = some absorbed ↔ b = row0.toBytes) ∧
    (∀ b, support b = some endpoint ↔ b = advanced.toBytes) := by
  have hl := byte_lengths
  have hs : squeezed.length = 33 := by
    simp [squeezed, squeezeA, Addr.toBytes_ofBytes, squeeze, bytes_length]
  have h01 : initial.toBytes ≠ row0.toBytes := by intro h; have := congrArg List.length h; omega
  have h02 : initial.toBytes ≠ advanced.toBytes := by intro h; have := congrArg List.length h; omega
  have h12 : row0.toBytes ≠ advanced.toBytes := by intro h; have := congrArg List.length h; omega
  have h0s : initial.toBytes ≠ squeezed := by intro h; have := congrArg List.length h; omega
  have h1s : row0.toBytes ≠ squeezed := by intro h; have := congrArg List.length h; omega
  have h2s : advanced.toBytes ≠ squeezed := by
    simp only [advanced, squeezed, advanceA, squeezeA, Addr.toBytes_ofBytes, advance, squeeze]
    simp
  have ha : answer ≠ s0 ∧ answer ≠ absorbed ∧ answer ≠ endpoint := by decide
  rcases state_distinct with ⟨hsa,hse,hsz,hae,haz,hez⟩
  refine ⟨?_,?_,?_⟩ <;> intro b <;> unfold support <;>
    split_ifs <;> simp_all only [Option.some.injEq, reduceCtorEq,
      Ne.symm hsa, Ne.symm hse, Ne.symm hae]

#print axioms support_fibers
end AspisR1.OraclePortRowAwareWitnessD2
end
