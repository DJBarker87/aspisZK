import R1TrailingStateFrame

/-! Byte-level P3 semantic initialization and canonical row-zero frames.
The Nat length encoder models four little-endian bytes. Its Rust and typed
public-input correspondence are separate obligations. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.PublicInitFrame
open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- ASCII `UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3`. -/
def domain : Bytes :=
  [85, 78, 80, 82, 79, 86, 69, 68, 58, 82, 49, 58, 80, 82, 73,
   86, 65, 84, 69, 45, 83, 65, 76, 84, 69, 68, 58, 83, 69, 77,
   65, 78, 84, 73, 67, 58, 80, 51]

def lengthBytes (n : Nat) : Bytes :=
  List.ofFn fun j : Fin 4 =>
    (⟨(n / 256^j.val) % 256, Nat.mod_lt _ (by decide)⟩ : Byte)

theorem lengthBytes_length (n : Nat) : (lengthBytes n).length = 4 := by
  simp [lengthBytes]

def pre (public : Bytes) : Bytes :=
  domain ++ [0] ++ lengthBytes public.length ++ public

theorem pre_length (public : Bytes) : (pre public).length = 43 + public.length := by
  simp [pre, domain, lengthBytes_length]

def frame (public : Bytes) (c1 : State) : Bytes :=
  TrailingStateFrame.frame (pre public) c1

theorem frame_length (public : Bytes) (c1 : State) :
    (frame public c1).length = 75 + public.length := by
  simp only [frame, TrailingStateFrame.frame, List.length_append, pre_length, bytes_length]
  omega

def addr {L : Nat} (public : Bytes) (hL : 75 + public.length ≤ L) (c1 : State) : Addr L :=
  Addr.ofBytes (frame public c1) (by rw [frame_length]; exact hL)

theorem addr_bytes {L : Nat} (public : Bytes) (hL : 75 + public.length ≤ L) (c1 : State) :
    (addr public hL c1).toBytes =
      domain ++ [0] ++ lengthBytes public.length ++ public ++ bytes c1 := by
  rw [addr, Addr.toBytes_ofBytes]
  rfl

/-- The tag and four-byte zero payload length of source row zero. -/
def emptyRecord : Bytes := [0, 0, 0, 0, 0]

def row0 {M Cv : Type} {L : Nat} (p : Params M Cv L) (hD : 5 ≤ p.D) (s : State) : Addr L :=
  absorbA p s 160 emptyRecord hD

theorem row0_bytes {M Cv : Type} {L : Nat} (p : Params M Cv L) (hD : 5 ≤ p.D) (s : State) :
    (row0 p hD s).toBytes = bytes s ++ [0, 160] ++ [0, 0, 0, 0, 0] := by
  rw [row0, absorbA, Addr.toBytes_ofBytes]
  rfl

theorem row0_prefix {M Cv : Type} {L : Nat} (p : Params M Cv L) (hD : 5 ≤ p.D) (s : State) :
    (row0 p hD s).toBytes.take 32 = bytes s := toBytes_absorbA p s 160 emptyRecord hD

#print axioms lengthBytes_length
#print axioms pre_length
#print axioms frame_length
#print axioms addr_bytes
#print axioms row0_bytes
#print axioms row0_prefix
end AspisR1.PublicInitFrame
end
