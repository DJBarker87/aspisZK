import R1Z.SharedGrammarBridgeBin

/-! Symbolic bottom-up ranks for the binary grammar. No leaf/node universe
is enumerated. These facts are independent of the missing phase interfaces. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.CausalTreeOrderBin
open R1Z.GamesR1PBin R1Z.LayoutR1PBin

/-- A dependency-layer rank, not a total enumeration of hash calls. -/
def layer : RIdx → ℕ
  | .inl b => b.val
  | .inr (.inl i) => 2 + i.val
  | .inr (.inr (.inl _)) => 5
  | .inr (.inr (.inr (.inl _))) => 6
  | .inr (.inr (.inr (.inr (_, n)))) => 7 + n.1.val

theorem child_before_parent (T : Fin 3) (n : NodeIdx) (j : Fin 2) :
    layer (childQ T n j) < layer (qNode T n) := by
  rcases n with ⟨⟨d, hd⟩, i⟩
  cases d with
  | zero => simp [childQ, layer, qLeaf, qNode]
  | succ d => simp [childQ, layer, qNode]

theorem child_before_root (T : Fin 3) (j : Fin 2) :
    layer (rootChild T j) < 24 := by
  simp [rootChild, layer, qNode]

theorem salt_before_leaf (T : Fin 3) (u : Fib) :
    layer (qSalt T u) < layer (qLeaf T u) := by
  simp [layer, qSalt, qLeaf]

/-- The ranked parent uses precisely the shared binary node bytes. -/
theorem shared_parent (rest : RIdx → R0Z.FsStatement.OracleAnswer)
    (T : Fin 3) (n : NodeIdx) :
    nodeBytes rest (childQ T n) =
      AspisR1.SharedBinaryRecordGrammar.nodeInput (fun j => rest (childQ T n j)) :=
  R1Z.SharedGrammarBridgeBin.node_eq rest (childQ T n)

#print axioms child_before_parent
#print axioms child_before_root
#print axioms salt_before_leaf
#print axioms shared_parent
end R1Z.CausalTreeOrderBin
