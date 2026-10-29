import R1Z.PV_RDCD4_RadixLoop
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD4_V220
open Aeneas Aeneas.Std Result PV_RDCD4_LazyComponents PV_RDCD4_RadixBlock

def source (poly : Array Q 28#usize) (challenge : Q) : Result Q := do
  let x2 ← F.square challenge
  let x3 ← F.mul challenge x2
  let x4 ← F.square x2
  let powers := Array.make 3#usize [challenge,x2,x3]
  let prepared ← F.prepare x4
  let acc ← block poly powers 6
  PV_RDCD4_RadixLoop.source poly powers prepared 6 acc

/-- Original loop-free radix-four reference; all concrete field and library
Result operations are retained, with no additional arbitrary callback. -/
def reference (poly : Array Q 28#usize) (challenge : Q) : Result Q := do
  let x2 ← F.square challenge
  let x3 ← F.mul challenge x2
  let x4 ← F.square x2
  let powers := Array.make 3#usize [challenge,x2,x3]
  let prepared ← F.prepare x4
  let acc ← block poly powers 6
  let acc ← PV_RDCD4_RadixLoop.step poly powers prepared 5 acc
  let acc ← PV_RDCD4_RadixLoop.step poly powers prepared 4 acc
  let acc ← PV_RDCD4_RadixLoop.step poly powers prepared 3 acc
  let acc ← PV_RDCD4_RadixLoop.step poly powers prepared 2 acc
  let acc ← PV_RDCD4_RadixLoop.step poly powers prepared 1 acc
  PV_RDCD4_RadixLoop.step poly powers prepared 0 acc

theorem source_reference (poly : Array Q 28#usize) (challenge : Q) :
    source poly challenge = reference poly challenge := by
  unfold source reference
  simp only [PV_RDCD4_RadixLoop.binding,PV_RDCD4_RadixLoop.finite,bind_assoc_eq]
  simp
#print axioms source_reference
end R1Z.PV_RDCD4_V220
