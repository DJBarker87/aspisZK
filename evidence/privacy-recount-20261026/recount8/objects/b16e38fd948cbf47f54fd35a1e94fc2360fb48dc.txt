import R1Z.LayoutTagR1PBin

/-! Counterexample to unconditionally separating binary nodes from abstract
duplex records. Only a 65-byte literal equality is reduced here. -/
set_option autoImplicit false
namespace R1Z.LayoutR1PBin
open R0Z.FsStatement R1Z.LensR1

/-- An abstract semantic absorb can equal a binary-node record. Wire lengths
are essential; first-byte separation cannot hold for arbitrary digests. -/
theorem binary_duplex_overlap :
    ∃ left right f : OracleAnswer, ∃ framed : List UInt8,
      [binTag] ++ ans left ++ ans right = ans f ++ [0, 0xa0] ++ framed := by
  refine ⟨(fun _ => 0), (fun i => if i.val = 0 then 0xa0 else 0),
    (fun i => if i.val = 0 then binTag else 0), List.replicate 31 0, ?_⟩
  decide

#print axioms binary_duplex_overlap
end R1Z.LayoutR1PBin
