import AuS1_Suffix
import RawJ_DigestRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawK_Head
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def head {A : Type} (p : Code A) := (observe (run p).1).head?

theorem lift_empty {A : Type} (r : Result A) : (run (monadLift r : Code A)).1 = [] := by
  cases r <;> rfl

theorem right {A B : Type} (p : Code A) (k : A → Code B) (out : B)
    (success : erase (p >>= k) = ok out)
    (empty : (run p).1 = [] := by apply AspisR1.RawK_Head.lift_empty) :
    ∃ a, erase p = ok a ∧ erase (k a) = ok out ∧
      ∀ entry, head (k a) = some entry → head (p >>= k) = some entry := by
  obtain ⟨a,hp,hk,logs⟩ := AuS1_Trace.success_bind _ _ _ success
  refine ⟨a,hp,hk,?_⟩
  intro entry h
  simpa only [head,logs,empty,List.nil_append] using h

theorem left {A B : Type} (p : Code A) (k : A → Code B) (out : B)
    (success : erase (p >>= k) = ok out) :
    ∀ entry, head p = some entry → head (p >>= k) = some entry := by
  obtain ⟨a,hp,hk,logs⟩ := AuS1_Trace.success_bind _ _ _ success
  intro entry h
  simp only [head,logs,AuS1_Trace.observe_append]
  cases observed : observe (run p).1 with
  | nil => simp only [head,observed,List.head?_nil] at h; cases h
  | cons first rest => simpa only [head,observed,List.cons_append,List.head?_cons] using h

theorem digest_head {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (hash : H) (parts : Slice (Slice U8)) (out : Array U8 32#usize)
    (success : erase (effects.digest D hash parts) = ok out) :
    head (effects.digest D hash parts) =
      some (AspisV8R19.SqueezeOracleBridge.flatten parts,
        AspisV8R19.SqueezeOracleBridge.decodeState out) := by
  cases call : D.digest hash parts with
  | fail e => simp only [effects,erase,call,bind_tc_fail] at success; cases success
  | div => simp only [effects,erase,call,bind_tc_div] at success; cases success
  | ok value =>
    simp only [effects,erase,call,bind_tc_ok] at success
    cases success
    simp only [head,effects,run,call,observe,List.flatMap_cons,List.flatMap_nil,List.singleton_append,List.head?_cons]

#print axioms lift_empty
#print axioms right
#print axioms left
#print axioms digest_head
end AspisR1.RawK_Head
end
