import R1Z.ProverCommitSimulatorCoin18
import R1Z.ProverCommitSaltBytes
import R1Z.LayoutR1P2Bin
import R1Z.QueryScanIdealHistory
import R1Z.RomFiniteBin
/-! Exact simulator coin addresses and finite-ROM coordinate transport.
This does not substitute a deterministic HOST_HASH for a random oracle or
assert that the runtime programs the table according to this model. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSimulatorOracle18
open R0Z R0Z.FsStatement R0Z.HvzkV R1Z.CouplingR1PBin
open R1Z.ProverCommitSimulatorCoin18
open R1Z.ProverCommitSaltBytes (byte)
attribute [local instance] Classical.propDecidable

/-- The five source slices are concatenated by HOST_HASH. Slice boundaries
are not part of the address, so injectivity below is on these actual bytes. -/
def address (seed : List UInt8) (attempt : Nat) (stream : UInt8) (counter : Nat) : List UInt8 :=
  domain.val.map byte ++ seed ++ R1Z.TranscriptR1.le32 attempt ++ [stream] ++
    R1Z.LayoutR1PBin.le64 counter

theorem source_frame (seed : Bytes32) (attempt : Aeneas.Std.U32)
    (stream : Aeneas.Std.U8) (counter : Aeneas.Std.U64) :
    ((frame seed attempt stream counter).val.flatMap (fun part => part.val.map byte)) =
      address (seed.val.map byte) attempt.val (byte stream) counter.val := by
  change domain.val.map byte ++ (seed.val.map byte ++
    ((Aeneas.Std.core.num.U32.to_le_bytes attempt).val.map byte ++
    ([byte stream] ++ ((Aeneas.Std.core.num.U64.to_le_bytes counter).val.map byte ++ [])))) = _
  rw [R1Z.ProverCommitSaltBytes.le32_source, R1Z.ProverCommitSaltBytes.le64_source]
  simp only [address, List.append_nil, List.append_assoc]

abbrev Index (count : Nat) := Fin 8 × Fin 4 × Fin count

def indexedAddress {count : Nat} (seed : OracleAnswer) (i : Index count) : List UInt8 :=
  address (List.ofFn seed) i.1.val (UInt8.ofNat i.2.1.val) i.2.2.val

theorem indexed_length {count : Nat} (seed : OracleAnswer) (i : Index count) :
    (indexedAddress seed i).length = 65 := by
  simp only [indexedAddress, address, List.length_append, List.length_map,
    List.length_ofFn, List.length_singleton]
  rfl

/-- Attempt, stream and counter remain distinct after byte concatenation,
provided the counter has not wrapped. No concrete address universe is read. -/
theorem indexed_injective {count : Nat} (room : count ≤ 2^64) (seed : OracleAnswer) :
    Function.Injective (indexedAddress (count := count) seed) := by
  intro i j same
  have body : R1Z.TranscriptR1.le32 i.1.val ++
      [UInt8.ofNat i.2.1.val] ++ R1Z.LayoutR1PBin.le64 i.2.2.val =
      R1Z.TranscriptR1.le32 j.1.val ++
      [UInt8.ofNat j.2.1.val] ++ R1Z.LayoutR1PBin.le64 j.2.2.val := by
    unfold indexedAddress address at same
    simpa only [List.append_assoc] using List.append_cancel_left
      (List.append_cancel_left (show domain.val.map byte ++
        (List.ofFn seed ++ (R1Z.TranscriptR1.le32 i.1.val ++
          ([UInt8.ofNat i.2.1.val] ++ R1Z.LayoutR1PBin.le64 i.2.2.val))) =
        domain.val.map byte ++
        (List.ofFn seed ++ (R1Z.TranscriptR1.le32 j.1.val ++
          ([UInt8.ofNat j.2.1.val] ++ R1Z.LayoutR1PBin.le64 j.2.2.val))) from by
        simpa only [List.append_assoc] using same))
  rw [List.append_assoc, List.append_assoc] at body
  obtain ⟨attempt, tail⟩ := List.append_inj body (by rfl)
  have ha : i.1 = j.1 := Fin.ext (R1Z.LayoutR1PBin.le32_inj _ _
    (lt_of_lt_of_le i.1.isLt (by norm_num))
    (lt_of_lt_of_le j.1.isLt (by norm_num)) attempt)
  have parts := List.cons.inj tail
  have stream := congrArg UInt8.toNat parts.1
  change i.2.1.val % 256 = j.2.1.val % 256 at stream
  have hi : i.2.1.val < 256 := lt_of_lt_of_le i.2.1.isLt (by norm_num)
  have hj : j.2.1.val < 256 := lt_of_lt_of_le j.2.1.isLt (by norm_num)
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at stream
  have hs : i.2.1 = j.2.1 := Fin.ext stream
  have hc : i.2.2 = j.2.2 := Fin.ext (R1Z.LayoutR1PBin.le64_inj _ _
    (lt_of_lt_of_le i.2.2.isLt room) (lt_of_lt_of_le j.2.2.isLt room) parts.2)
  exact Prod.ext ha (Prod.ext hs hc)

def key {count : Nat} (bound : Nat) (fits : 65 ≤ bound) (seed : OracleAnswer)
    (i : Index count) : R1Z.RomFiniteBin.Address bound :=
  ⟨indexedAddress seed i, (R1Z.RomFiniteBin.mem_domain bound (indexedAddress seed i)).mpr
    (by simpa only [indexed_length] using fits)⟩

theorem key_injective {count : Nat} (room : count ≤ 2^64)
    (bound : Nat) (fits : 65 ≤ bound) (seed : OracleAnswer) :
    Function.Injective (key (count := count) bound fits seed) := by
  intro i j same
  exact indexed_injective room seed (congrArg Subtype.val same)

/-- Under the explicit uniform finite random-oracle table law, these source
coin requests have the independent coordinate law used by the model. The
seed is fixed, not a replacement for the table's randomness. -/
theorem coins_uniform {Answer : Type} [Fintype Answer] [Nonempty Answer]
    {count : Nat} (room : count ≤ 2^64)
    (bound : Nat) [finiteAddress : Fintype (R1Z.RomFiniteBin.Address bound)]
    (fits : 65 ≤ bound) (seed : OracleAnswer) :
    MP (fun table : R1Z.RomFiniteBin.Address bound → Answer =>
      fun i : Index count => table (key bound fits seed i)) := by
  intro f
  have he := R1Z.QueryScanIdealHistory.coordinates_uniform (U := Answer)
    (key bound fits seed) (key_injective room bound fits seed) f
  convert he using 1 <;> apply R1Z.QueryScanIdealHistory.mean_fintype_transport

#print axioms source_frame
#print axioms indexed_length
#print axioms indexed_injective
#print axioms key_injective
#print axioms coins_uniform
end R1Z.ProverCommitSimulatorOracle18
