import BinMerkle32Leaf
import FS2.Verifier

/-! Mirrors `MerkleProgram.lean`; see design/BIN-COMMITMENT-MODEL-20261019.md for line pins.
 Oracle programs for the ordered input trace of a Merkle32 path. -/
set_option autoImplicit false
namespace AspisR1.BinMerkleProgram

open AspisR1.BinMerkle32Path AspisR1.BinMerkle32Leaf
open AspisV8R19.MemoizedProgramLaw

def pathProgram : {slots : List (Fin 2)} → Path slots → Digest →
    Program (List AspisR1.BinMerkle32Path.Byte) Digest Digest
  | [], .nil, current => .done current
  | slot :: slots, @Path.cons .(slot) .(slots) siblings tail, current =>
      .ask (nodeInput (fillChild slot siblings current)) fun digest =>
        pathProgram tail digest

def leafProgram {slots : List (Fin 2)} (path : Path slots)
    (leaf : List AspisR1.BinMerkle32Path.Byte) :
    Program (List AspisR1.BinMerkle32Path.Byte) Digest Digest :=
  .ask leaf fun digest => pathProgram path digest

theorem eval_pathProgram (H : List AspisR1.BinMerkle32Path.Byte → Digest)
    {slots : List (Fin 2)}
    (path : Path slots) : ∀ current,
    eval H (pathProgram path current) =
      ((inputTrace H path current).map fun input => (input, H input),
        foldPath H path current) := by
  induction path with
  | nil => intro current; rfl
  | @cons slot slots siblings tail ih =>
      intro current
      simp only [pathProgram, eval, inputTrace, foldPath]
      rw [ih]
      simp only [Prod.fst, Prod.snd, List.map_cons]

theorem eval_leafProgram (H : List AspisR1.BinMerkle32Path.Byte → Digest)
    {slots : List (Fin 2)} (path : Path slots)
    (leaf : List AspisR1.BinMerkle32Path.Byte) :
    eval H (leafProgram path leaf) =
      ((fullTrace H path leaf).map fun input => (input, H input),
        foldPath H path (H leaf)) := by
  simp only [leafProgram, eval, fullTrace]
  rw [eval_pathProgram]
  simp only [Prod.fst, Prod.snd, List.map_cons]

theorem pathProgram_accepts_iff (H : List AspisR1.BinMerkle32Path.Byte → Digest)
    {slots : List (Fin 2)}
    (path : Path slots) (current root : Digest) :
    (eval H (pathProgram path current)).2 = root ↔
      foldPath H path current = root := by
  rw [eval_pathProgram]

theorem leafProgram_accepts_iff (H : List AspisR1.BinMerkle32Path.Byte → Digest)
    {slots : List (Fin 2)} (path : Path slots)
    (leaf : List AspisR1.BinMerkle32Path.Byte) (root : Digest) :
    (eval H (leafProgram path leaf)).2 = root ↔
      foldPath H path (H leaf) = root := by
  rw [eval_leafProgram]


#print axioms eval_pathProgram
#print axioms eval_leafProgram
#print axioms pathProgram_accepts_iff
#print axioms leafProgram_accepts_iff

end AspisR1.BinMerkleProgram
