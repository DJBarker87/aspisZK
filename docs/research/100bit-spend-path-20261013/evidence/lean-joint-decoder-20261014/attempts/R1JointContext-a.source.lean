import R1OpeningPrefixCompletion
import R1IndexedMessage
import R1DuplexSeek

/-! Read the joint prefix context from a queried address and the preceding
table. The query and next message use their recovered indices and require
canonical abstract encodings. No oracle is an input to this decoder. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.JointContext
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

structure Context (M : Type) (L : Nat) where
  endpoint : State
  queryAddress : Addr L
  c1 : State
  records : List (Rec M)
  queryMessage : M
  nextMessage : M

def parse (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (semanticFuel openingFuel : Nat) (c : Addr L) (T : Table (Addr L) State) :
    Option (Context M L) := do
  let (endpoint, nextLabel, nextData) ← parseAbsorb c
  let (a, _) ← DuplexSeek.seek p T 9 endpoint
  let (previous, queryLabel, queryData) ← parseAbsorb a
  let (c1, rs) ← OpeningPrefixCompletion.typed p pubBytes tag T
    semanticFuel openingFuel previous
  let qm ← IndexedMessage.read p rs.length queryLabel queryData
  let nm ← IndexedMessage.read p (rs.length + 1) nextLabel nextData
  return ⟨endpoint, a, c1, rs, qm, nm⟩

theorem parse_of_checks (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (semanticFuel openingFuel : Nat) (c : Addr L) (T : Table (Addr L) State)
    (endpoint : State) (nl : Byte) (nd : Bytes) (a : Addr L) (xs : List State)
    (previous : State) (ql : Byte) (qd : Bytes) (c1 : State) (rs : List (Rec M))
    (qm nm : M)
    (hc : parseAbsorb c = some (endpoint, nl, nd))
    (hs : DuplexSeek.seek p T 9 endpoint = some (a, xs))
    (ha : parseAbsorb a = some (previous, ql, qd))
    (ht : OpeningPrefixCompletion.typed p pubBytes tag T semanticFuel openingFuel previous =
      some (c1, rs))
    (hq : IndexedMessage.read p rs.length ql qd = some qm)
    (hn : IndexedMessage.read p (rs.length + 1) nl nd = some nm) :
    parse p pubBytes tag semanticFuel openingFuel c T =
      some ⟨endpoint, a, c1, rs, qm, nm⟩ := by
  simp only [parse, hc, hs, ha, ht, hq, hn, Option.bind_some]

theorem parse_encoded (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (semanticFuel openingFuel : Nat) (T : Table (Addr L) State)
    (endpoint previous c1 : State) (rs : List (Rec M)) (qm nm : M)
    (xs : List State)
    (hs : DuplexSeek.seek p T 9 endpoint =
      some (absorbA p previous (p.lbl rs.length) (p.enc qm) (p.encLen qm), xs))
    (ht : OpeningPrefixCompletion.typed p pubBytes tag T semanticFuel openingFuel previous =
      some (c1, rs)) :
    parse p pubBytes tag semanticFuel openingFuel
      (absorbA p endpoint (p.lbl (rs.length + 1)) (p.enc nm) (p.encLen nm)) T =
      some ⟨endpoint, absorbA p previous (p.lbl rs.length) (p.enc qm) (p.encLen qm),
        c1, rs, qm, nm⟩ := by
  exact parse_of_checks p pubBytes tag semanticFuel openingFuel _ T endpoint _ _ _ xs
    previous _ _ c1 rs qm nm (parseAbsorb_absorbA p endpoint _ _ _) hs
    (parseAbsorb_absorbA p previous _ _ _) ht
    (IndexedMessage.read_encoded p rs.length qm)
    (IndexedMessage.read_encoded p (rs.length + 1) nm)

#print axioms parse_of_checks
#print axioms parse_encoded
end AspisR1.JointContext
end
