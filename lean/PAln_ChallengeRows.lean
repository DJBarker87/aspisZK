import PAln_SourceRun
import PAln_TypedRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_ChallengeRows
open AspisR1PublicPreparation
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1.TranscriptView

def semantic {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre)) : List LiteralTranscript.Challenge :=
  cs.map (fun c => (.ordinary (SourceLiteralTraceLift.sourceChallenge c),decodeState c.after.state))

def suffix (values : Fin 6 → LiteralTranscript.E) (states : Fin 8 → State)
    (queries : List Nat) (rho : LiteralTranscript.E) : List LiteralTranscript.Challenge :=
  [(.ordinary (values 0),states 0),(.ordinary (values 1),states 1),
   (.ordinary (values 2),states 2),(.ordinary (values 3),states 3),
   (.ordinary (values 4),states 4),(.ordinary (values 5),states 5),
   (.queries (.ok queries),states 6),(.ordinary rho,states 7)]

def atRow {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre)) (values : Fin 6 → LiteralTranscript.E)
    (states : Fin 8 → State) (queries : List Nat) (rho : LiteralTranscript.E)
    (row : Nat) : LiteralTranscript.Challenge :=
  (semantic cs++suffix values states queries rho)[row]?.getD (.ordinary 0,0)

theorem length {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre)) (count : cs.length=25)
    (values : Fin 6 → LiteralTranscript.E) (states : Fin 8 → State)
    (queries : List Nat) (rho : LiteralTranscript.E) :
    (semantic cs++suffix values states queries rho).length=33 := by
  simp only [semantic,List.length_append,List.length_map,count,suffix,List.length_cons,List.length_nil]

theorem source_entry {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre)) (count : cs.length=25)
    (values : Fin 6 → LiteralTranscript.E) (states : Fin 8 → State)
    (queries : List Nat) (rho : LiteralTranscript.E) (row : Nat)
    (c : SourceFull25.Call D pre) (slot : cs[row]?=some c) :
    atRow cs values states queries rho row=
      (.ordinary (SourceLiteralTraceLift.sourceChallenge c),decodeState c.after.state) := by
  have below := (List.getElem?_eq_some_iff.mp slot).choose
  have len : (semantic cs).length=25 := by simp only [semantic,List.length_map,count]
  unfold atRow
  rw [List.getElem?_append_left (by omega : row<(semantic cs).length)]
  simp only [semantic,List.getElem?_map,slot,Option.map_some,Option.getD_some]

theorem ordinary {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre)) (count : cs.length=25)
    (values : Fin 6 → LiteralTranscript.E) (states : Fin 8 → State)
    (queries : List Nat) (rho : LiteralTranscript.E) (row : Nat) (below : row<31) :
    ∃ value,(atRow cs values states queries rho row).1=Value.ordinary value := by
  by_cases first : row<25
  · let c := cs[row]'(by omega)
    have slot : cs[row]?=some c := List.getElem?_eq_some_iff.mpr ⟨by omega,rfl⟩
    rw [source_entry cs count values states queries rho row c slot]
    exact ⟨_,rfl⟩
  · have len : (semantic cs).length=25 := by simp only [semantic,List.length_map,count]
    simp only [atRow,List.getElem?_append_right (by omega : (semantic cs).length≤row),len]
    have cases : row=25 ∨ row=26 ∨ row=27 ∨ row=28 ∨ row=29 ∨ row=30 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨_,rfl⟩

#print axioms length
#print axioms source_entry
#print axioms ordinary
end AspisR1.PAln_ChallengeRows
end
