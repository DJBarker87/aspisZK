import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue001
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_entropy.Profile21SourceExpander.new`.
Recursive calls remain the original extracted calls. -/
def continueAfter (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (seed : Array Std.U8 32#usize) (out : Payload (zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) seed)) : Result aspis_prover.state_only_entropy.Profile21SourceExpander := do
  let z := out
  let a := Array.repeat 32#usize 0#u8
  ok { hash, seed := z, counter := 0#u64, block := a, word := 8#usize }

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (seed : Array Std.U8 32#usize) :
    aspis_prover.state_only_entropy.Profile21SourceExpander.new (hash := hash) (seed := seed) =
      (zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) seed >>= fun out => continueAfter (hash := hash) (seed := seed) out) := by
  rw [aspis_prover.state_only_entropy.Profile21SourceExpander.new]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (seed : Array Std.U8 32#usize) (out : Payload (zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) seed))
    (h : (zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) seed) = .ok out) :
    aspis_prover.state_only_entropy.Profile21SourceExpander.new (hash := hash) (seed := seed) = continueAfter (hash := hash) (seed := seed) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (seed : Array Std.U8 32#usize) (e : Error)
    (h : (zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) seed) = .fail e) :
    aspis_prover.state_only_entropy.Profile21SourceExpander.new (hash := hash) (seed := seed) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (seed : Array Std.U8 32#usize)
    (h : (zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) seed) = .div) :
    aspis_prover.state_only_entropy.Profile21SourceExpander.new (hash := hash) (seed := seed) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue001
