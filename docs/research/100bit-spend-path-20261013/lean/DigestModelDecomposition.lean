import TerminalDigestFrontierModel

/-! Generic field-level decomposition of the retained complete digest model.
No concrete extension-field reduction or numerical certificate is used. -/
set_option autoImplicit false
namespace AspisR1.DigestModelDecomposition
variable {K : Type} [Field K]

abbrev foldStep (pub : R0P.Public K) (o : R0P.Openings K) (sel : R0P.Sel K)
    (acc : R0P.Digest K) (key : R0P.DigestKey) : R0P.Digest K :=
  R0P.digestAddBinding acc (sel (R0P.digestRow pub key)) o.z
    (R0P.digestStart pub key) (R0P.digestTarget pub key)

def prefixKeys (pub : R0P.Public K) : List R0P.DigestKey :=
  [.anchor, .nullifier] ++
    (match pub.recipient with | none => [] | some _ => [.recipient]) ++ [.change]

def suffixKeys (pub : R0P.Public K) : List R0P.DigestKey :=
  [.nextRoot] ++ (if R0P.digestCarry pub.nextPairIndex < 20 then [.carry] else [])

def prefixFold (pub : R0P.Public K) (o : R0P.Openings K) (sel : R0P.Sel K) : R0P.Digest K :=
  (prefixKeys pub).foldl (foldStep pub o sel) (fun _ => 0)

def suffixFold (pub : R0P.Public K) (o : R0P.Openings K) (sel : R0P.Sel K)
    (acc : R0P.Digest K) : R0P.Digest K :=
  (suffixKeys pub).foldl (foldStep pub o sel) acc

/-- The recursive twenty-level model is the original ordered frontier fold. -/
theorem frontier_twenty_eq_fold (pub : R0P.Public K) (o : R0P.Openings K)
    (sel : R0P.Sel K) (acc : R0P.Digest K) :
    AspisR1TerminalDigestPublicLoop.Model.frontierPrefix pub o sel 20 acc =
      AspisR1TerminalDigestPublicLoop.Model.publicFrontierFold pub o sel acc := by
  rfl

/-- The original complete model contains exactly prefix, frontier and suffix,
including both optional branches in their original positions. -/
theorem complete_decomposition (pub : R0P.Public K) (o : R0P.Openings K)
    (sel : R0P.Sel K) :
    R0P.publicDigestLanes pub o sel =
      suffixFold pub o sel
        (AspisR1TerminalDigestPublicLoop.Model.frontierPrefix pub o sel 20
          (prefixFold pub o sel)) := by
  rw [frontier_twenty_eq_fold]
  unfold R0P.publicDigestLanes R0P.digestKeys suffixFold prefixFold prefixKeys suffixKeys
    AspisR1TerminalDigestPublicLoop.Model.publicFrontierFold
    AspisR1TerminalDigestPublicLoop.Model.frontierKeys foldStep
  simp only [List.foldl_append]
  rfl

#print axioms frontier_twenty_eq_fold
#print axioms complete_decomposition
end AspisR1.DigestModelDecomposition
