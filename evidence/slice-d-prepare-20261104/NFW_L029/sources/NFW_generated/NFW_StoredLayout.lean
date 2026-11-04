import NFW_Bind
set_option autoImplicit false
namespace AspisR1.NFW_StoredLayout
/-- Frozen compact format offsets. Values are source constants, not a new wire format. -/
def logicalSemantic : Nat := 12903+29*32
def compactSemantic : Nat := logicalSemantic-16*(1+10*28+(87+29)+29)
def semantic : Nat := 16
def y1 : Nat := semantic+compactSemantic
def inactive : Nat := y1+29*16
def round0 : Nat := inactive+32
def folded : Nat := round0+224
def round1 : Nat := folded+32
def finalMessage : Nat := round1+224
def openings : Nat := finalMessage+64*32
def nodes : Nat := openings+22*832
def proofBytes : Nat := nodes+32*(146+146+128+172+172+150)
def windows : List (Nat×Nat) := [(semantic,compactSemantic),(y1,464),(inactive,32),(round0,224),(folded,32),(round1,224),(finalMessage,2048)]
theorem exact_offsets :
 logicalSemantic=13831 ∧ compactSemantic=7015 ∧ semantic=16 ∧ y1=7031 ∧ inactive=7495 ∧
 round0=7527 ∧ folded=7751 ∧ round1=7783 ∧ finalMessage=8007 ∧ openings=10055 ∧ nodes=28359 ∧ proofBytes=57607 := by decide
theorem bounds (start width : Nat) (inside : (start,width)∈windows) : start+width≤proofBytes := by
 simp only [windows,List.mem_cons,List.not_mem_nil,or_false] at inside
 rcases inside with h|h|h|h|h|h|h <;> cases h <;> decide
theorem logical_split : logicalSemantic+928=14759 := by decide
theorem folded_payload : 32+224=256 := by decide
#print axioms exact_offsets
#print axioms bounds
#print axioms logical_split
#print axioms folded_payload
end AspisR1.NFW_StoredLayout
