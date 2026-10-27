import AuS1_Suffix
import RawJ_DigestRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawK_Head
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def head {A : Type} (p : Code A) := (observe (run p).1).head?

theorem lift_empty {A : Type} (r : Result A) : (run (AspisR1PublicPreparation.PreparedHashCode.lift r)).1 = [] := by
  cases r <;> rfl

theorem right {A B : Type} (r : Result A) (k : A → Code B) (out : B)
    (success : erase ((AspisR1PublicPreparation.PreparedHashCode.lift r : Code A) >>= k) = ok out) :
    ∃ a, r = ok a ∧ erase (k a) = ok out ∧
      head ((AspisR1PublicPreparation.PreparedHashCode.lift r : Code A) >>= k) = head (k a) := by
  obtain ⟨a,hp,hk,logs⟩ := AuS1_Trace.success_bind _ _ _ success
  rw [erase_lift] at hp
  refine ⟨a,hp,hk,?_⟩
  simp only [head,logs,lift_empty,List.nil_append]

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
    simp only [effects,erase,call,bind_tc_ok,erase_pure] at success
    cases success
    simp only [head,effects,run,call,observe,List.flatMap_cons,List.flatMap_nil,List.singleton_append,List.head?_cons]

#print axioms lift_empty
#print axioms right
#print axioms digest_head
end AspisR1.RawK_Head
end
