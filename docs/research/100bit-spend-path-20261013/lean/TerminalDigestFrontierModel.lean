import R0P.Digest

/-! Symbolic model for the actual outer twenty-level digest loop.  This keeps
frontier accumulation recursive rather than evaluating 160 field cells. -/
set_option autoImplicit false
namespace AspisR1TerminalDigestPublicLoop.Model
abbrev Digest (K : Type) := R0P.Digest K
abbrev Public (K : Type) := R0P.Public K
abbrev Openings (K : Type) := R0P.Openings K
abbrev Sel (K : Type) := R0P.Sel K

def frontierStep {K : Type} [Field K] (pub : Public K) (o : Openings K) (sel : Sel K)
    (acc : Digest K) (level : Fin 20) : Digest K :=
  R0P.digestAddBinding acc (sel (R0P.digestRow pub (.frontier level))) o.z
    (R0P.digestStart pub (.frontier level)) (R0P.digestTarget pub (.frontier level))

def frontierPrefix {K : Type} [Field K] (pub : Public K) (o : Openings K) (sel : Sel K) :
    Nat → Digest K → Digest K
  | 0, acc => acc
  | n + 1, acc =>
      frontierStep pub o sel (frontierPrefix pub o sel n acc)
        ⟨n % 20, Nat.mod_lt _ (by norm_num)⟩

theorem frontierPrefix_zero {K : Type} [Field K] (pub : Public K) (o : Openings K) (sel : Sel K)
    (acc : Digest K) : frontierPrefix pub o sel 0 acc = acc := rfl

theorem frontierPrefix_succ {K : Type} [Field K] (pub : Public K) (o : Openings K) (sel : Sel K)
    (n : Nat) (acc : Digest K) (hn : n < 20) :
    frontierPrefix pub o sel (n+1) acc =
      frontierStep pub o sel (frontierPrefix pub o sel n acc) ⟨n, hn⟩ := by
  simp only [frontierPrefix, Nat.mod_eq_of_lt hn]

def frontierKeys : List (R0P.DigestKey) := List.ofFn R0P.DigestKey.frontier

def publicFrontierFold {K : Type} [Field K] (pub : Public K) (o : Openings K) (sel : Sel K) (acc : Digest K) : Digest K :=
  frontierKeys.foldl (fun state key =>
    R0P.digestAddBinding state (sel (R0P.digestRow pub key)) o.z
      (R0P.digestStart pub key) (R0P.digestTarget pub key)) acc

#print axioms frontierPrefix_succ
end AspisR1TerminalDigestPublicLoop.Model
