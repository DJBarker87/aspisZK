import NIT_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignPair
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts

/-- The native argument cut is insensitive to the regular post payload, apart
from canonicality. Thus it cannot supply the post payload needed by Trace.returned. -/
theorem regular_post_free (w : Ref W) (alpha : Ref (Array E 2#usize))
 (f : Ref (Slice U8)) (scratch : Ref (Array K 64#usize)) (parts : Ref Parts)
 (ap0 ap1 : Powers) (common : Ref CommonCells) (shared : Bool)
 (power i : Nat) (l : PairEdges) (replacement : Parts)
 (cut : cutPairEdges w alpha f scratch parts ap0 ap1 common shared power i l)
 (canon : canonical replacement) :
 cutPairEdges w alpha f scratch parts ap0 ap1 common shared power i
  { l with regular_post := replacement } := by
 rcases cut with ⟨s2,hp,hi,ca,c0,c1,cp,_,cq,size,rest⟩
 exact ⟨s2,hp,hi,ca,c0,c1,cp,canon,cq,size,rest⟩

/-- This is an obstruction to identifying a fixed payload from the cut, not a
counterexample to the frozen implementation. All native observations stay fixed. -/
theorem regular_post_not_determined (w : Ref W) (alpha : Ref (Array E 2#usize))
 (f : Ref (Slice U8)) (scratch : Ref (Array K 64#usize)) (parts : Ref Parts)
 (ap0 ap1 : Powers) (common : Ref CommonCells) (shared : Bool)
 (power i : Nat) (l : PairEdges) (replacement : Parts)
 (cut : cutPairEdges w alpha f scratch parts ap0 ap1 common shared power i l)
 (canon : canonical replacement) (different : replacement ≠ l.regular_post) :
 ∃ other : PairEdges,
 cutPairEdges w alpha f scratch parts ap0 ap1 common shared power i other ∧
 other.regular_post ≠ l.regular_post ∧ other.who=l.who ∧ other.parts=l.parts := by
 exact ⟨{ l with regular_post := replacement },
  regular_post_free w alpha f scratch parts ap0 ap1 common shared power i l replacement cut canon,
  different,rfl,rfl⟩

/-- Reaching partials requires a shared guard and a returning regular success.
No assertion about an unreached child reply is used. -/
theorem partial_reached (shared : Bool) (l : SameGuard) (out : Reply Unit)
 (cut : cutSameGuard shared l out) (reached : 3 ≤ l.count) :
 shared=true ∧ l.regular=.Ok () := by
 rcases cut with ⟨_,_,count,_⟩
 cases regular : l.regular with
 | Err e => simp [sameExpected,regular] at count; omega
 | Ok u =>
  cases u
  cases shared with
  | false => simp [sameExpected,regular] at count; omega
  | true => exact ⟨rfl,rfl⟩

/-- Reaching high additionally requires the actual partial reply to succeed. -/
theorem high_reached (shared : Bool) (l : SameGuard) (out : Reply Unit)
 (cut : cutSameGuard shared l out) (reached : 4 ≤ l.count) :
 shared=true ∧ l.regular=.Ok () ∧ l.«partial»=.Ok () := by
 obtain ⟨hs,hr⟩ := partial_reached shared l out cut (by omega)
 rcases cut with ⟨_,_,count,_⟩
 subst shared
 cases hp : l.«partial» with
 | Err e => simp [sameExpected,hr,hp] at count; omega
 | Ok u => cases u; exact ⟨rfl,hr,rfl⟩

#print axioms regular_post_free
#print axioms regular_post_not_determined
#print axioms partial_reached
#print axioms high_reached
end AspisR1.NIW_AlignPair
