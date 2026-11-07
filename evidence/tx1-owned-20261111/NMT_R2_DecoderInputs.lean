import NMT_R2_InputSlice
import NMT_345Decoder
set_option autoImplicit false
noncomputable section
namespace NMT_R2_DecoderInputs
open Aeneas Aeneas.Std RSL NMT_R2_Bytes

def window (bytes : Bytes) (length : bytes.length = 1880) (lo hi : Nat) : Slice U8 :=
 ⟨native (slice bytes lo hi),by
  have bound : 1880 ≤ Usize.max := by scalar_tac
  simp only [native,List.length_map,slice,List.length_take,List.length_drop,length]
  omega⟩

def anchor (bytes : Bytes) (length : bytes.length = 1880) : Array U8 32#usize :=
 ⟨(window bytes length 112 144).val,by
  simp [window,native,slice,length]⟩

def terminalHeader (b : Bytes) : Bool :=
 b.length == 1880 && b.take 4 == [65,83,70,56] && b.getD 4 0 == 1 &&
 (b.getD 5 0 == 1 || b.getD 5 0 == 2) && b.getD 6 0 == 1

/-- Exact 32-byte late header: source checks byte fields, LE lengths and all
reserved bytes before it calls the live-snapshot decoder. -/
def lateHeader (b : Bytes) : Bool :=
 slice b 144 176 == [65,83,80,76,65,84,69,49,1,2,32,0,32,3,0,0,
  176,2,0,0,240,5,0,0,0,0,0,0,0,0,0,0]

/-- Source prefix up to the FIRST Box site. Later decoder rejection does not
undo having reached that site. Exact emitted-prefix association is separate. -/
def firstAllocation (bytes : Bytes) : Bool :=
 if h : bytes.length = 1880 then
  if terminalHeader bytes && lateHeader bytes then
   match AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical (anchor bytes h) with
   | .ok (.Ok _) =>
    match AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1
     (window bytes h 176 976) with
    | .ok (.Ok _) => true
    | _ => false
   | _ => false
  else false
 else false

theorem firstAllocation_wrong_length (bytes : Bytes) (h : bytes.length ≠ 1880) :
 firstAllocation bytes = false := by
 unfold firstAllocation
 rw [dif_neg h]
#print axioms firstAllocation_wrong_length
end NMT_R2_DecoderInputs
end
