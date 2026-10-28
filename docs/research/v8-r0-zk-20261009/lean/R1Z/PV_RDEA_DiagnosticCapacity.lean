import R1Z.PV_RDEA_CapacityEndpoint
namespace R1Z.PV_RDEA_DiagnosticCapacity

/-- Decoded fmt template metadata. Rendered argument values are absent from
estimated_capacity's traversal. The parser-to-template bridge is separate. -/
inductive Piece where
  | literal (bytes : Nat)
  | placeholder

def scan : List Piece → Nat → Bool → Nat × Bool
  | [],len,starts => (len,starts)
  | .literal n::rest,len,starts => scan rest (len+n) starts
  | .placeholder::rest,len,starts => scan rest len (starts || len=0)

def estimate (template : List Piece) : Nat :=
  let (len,starts) := scan template 0 false
  if starts && len<16 then 0 else (len*2)%18446744073709551616

/-- The hex formatting template contains no literal bytes, hence no initial
allocation for each byte's formatting, independently of that byte. -/
theorem hex_capacity : estimate [.placeholder]=0 := rfl

theorem hex_request_word : PV_RDEA_CapacityEndpoint.requestSizes (estimate [.placeholder])=[] := by
  rw [hex_capacity]
  simp [PV_RDEA_CapacityEndpoint.requestSizes]

/-- Debug build-id path: 23-byte prefix, six-byte suffix, one slash and two
hex bytes per public ELF build-id byte. -/
def buildIdCapacity (publicIdLength : Nat) := 23+6+2*publicIdLength+1

theorem build_id_length (n : Nat) : buildIdCapacity n=2*n+30 := by unfold buildIdCapacity; omega

#print axioms hex_capacity
#print axioms hex_request_word
#print axioms build_id_length
end R1Z.PV_RDEA_DiagnosticCapacity
