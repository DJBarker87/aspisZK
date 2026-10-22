import R1Z.ProverCommitPublicCoins41
import R1Z.LayoutR1P3Bin

/-! Reusing public binding answers does not change the verifier's opened
commitment log. The independent spare binding coordinates remain available
to the middle carrier without becoming observable. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitBindingErase41
open R0Z.FsStatement R1Z.GamesR1PBin R1Z.LayoutR1PBin R1Z.LensR1
attribute [local instance] Classical.propDecidable

def rebind (first second : OracleAnswer) (rest : RIdx → OracleAnswer) : RIdx → OracleAnswer
  | .inl b => if b.val = 0 then first else second
  | .inr q => rest (.inr q)

theorem rebind_child (first second : OracleAnswer) (rest : RIdx → OracleAnswer)
    (t : Fin 3) (n : NodeIdx) (j : Fin 2) :
    rebind first second rest (childQ t n j) = rest (childQ t n j) := by
  rcases n with ⟨⟨d,hd⟩,i⟩
  cases d <;> rfl

/-- Includes roots, leaves and internal nodes; no leaf/node universe is
normalised. Both the public nonce and the private seeds can differ here. -/
theorem opened_address {e1 e2 : Nat} (pub : List UInt8) (tag : UInt8)
    (lv : Fin 3 → Fib → List UInt8) (sec sec' : SecP) (digest : OracleAnswer)
    (rest : RIdx → OracleAnswer) (first second : OracleAnswer)
    (fib : Fin 3 → Finset Fib) (c : CPos e1 e2) (opened : openedC fib c) :
    gram pub tag lv sec digest (rebind first second rest) c =
      gram pub tag lv sec' digest rest c := by
  rcases c with T | (c | c) | (b | i | ⟨T,u⟩ | ⟨T,u⟩ | ⟨T,n⟩)
  · rfl
  · cases opened
  · cases opened
  · cases opened
  · cases opened
  · cases opened
  · rfl
  · simp only [gram,nodeBytes,rebind_child]

def answer (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer) :
    Fin 3 ⊕ RIdx → OracleAnswer
  | .inl t => roots t
  | .inr q => rest q

theorem opened_answer (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer)
    (first second : OracleAnswer) (fib : Fin 3 → Finset Fib)
    (c : Fin 3 ⊕ RIdx) (opened : openedQ fib c) :
    answer roots (rebind first second rest) c = answer roots rest c := by
  rcases c with t | (b | i | salt | leaf | node)
  · rfl
  · cases opened
  · cases opened
  · cases opened
  · rfl
  · rfl

/-- Complete ordered verifier commitment observations retain repeats and
opening order. Independent latent binding coins can therefore be erased
from this observable without changing it. -/
theorem opened_log {e1 e2 : Nat} (pub : List UInt8) (tag : UInt8)
    (lv : Fin 3 → Fib → List UInt8) (sec sec' : SecP) (digest : OracleAnswer)
    (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer)
    (first second : OracleAnswer) (fib : Fin 3 → Finset Fib)
    (reads : List (Fin 3 ⊕ RIdx)) (covered : ∀ c ∈ reads, openedQ fib c) :
    reads.map (fun c => (gram pub tag lv sec digest (rebind first second rest)
      (cposOf c : CPos e1 e2),answer roots (rebind first second rest) c)) =
    reads.map (fun c => (gram pub tag lv sec' digest rest
      (cposOf c : CPos e1 e2),answer roots rest c)) := by
  apply List.map_congr_left
  intro c member
  exact Prod.ext
    (opened_address pub tag lv sec sec' digest rest first second fib (cposOf c)
      ((openedC_cposOf fib c).mpr (covered c member)))
    (opened_answer roots rest first second fib c (covered c member))

#print axioms rebind_child
#print axioms opened_address
#print axioms opened_answer
#print axioms opened_log
end R1Z.ProverCommitBindingErase41
