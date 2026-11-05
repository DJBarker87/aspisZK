import NHY_ErrorFragments
import NHY_StringAppend
set_option autoImplicit false
noncomputable section
namespace NIJ_FormatterPackets
open Aeneas Aeneas.Std Result
abbrev E := NGL_ErrorModel.E

def code : E → Nat
 | .Parse => 2 | .Semantic => 3 | .Transcript => 4 | .Relation => 5
 | .Merkle => 6 | .Query => 7 | .Checkpoint => 8 | .Allocation => 9

def fragmentCode (s : String) : Nat :=
 if s="r1:error:" then 1 else if s="Parse" then 2 else
 if s="Semantic" then 3 else if s="Transcript" then 4 else
 if s="Relation" then 5 else if s="Merkle" then 6 else
 if s="Query" then 7 else if s="Checkpoint" then 8 else
 if s="Allocation" then 9 else 0

/-- The String-receiver local log identifies the actual ordered literals.
This is a packet interpretation, not native byte-production credit. -/
theorem string_log (e : E) :
 (NHY_ErrorFragments.fragments e).map fragmentCode = [1,code e] := by
 cases e <;> decide

/-- Every deployed label has an exact, finite UTF8 literal. -/
theorem decoded_bytes (e : E) :
 (String.join (NHY_ErrorFragments.fragments e)).toUTF8 =
 (NGL_ErrorModel.message e).toUTF8 := NHY_ErrorFragments.syscall_bytes e

/-- Cleanup may follow the returning syscall only; failing and diverging
runtime calls have no suffix. This retains the complete Result carrier. -/
def finish {S : Type} (syscall : String → S → Result S)
 (cleanup : S → Result S) (e : E) (s : S) : Result (NGL_ErrorModel.PE × S) := do
 let logged ← syscall (NGL_ErrorModel.message e) s
 let released ← cleanup logged
 ok (.InvalidInstructionData,released)

theorem abort_prefix {S : Type} (syscall : String → S → Result S)
 (cleanup : S → Result S) (e : E) (s : S) :
 finish syscall cleanup e s = match syscall (NGL_ErrorModel.message e) s with
 | .ok after => do let released ← cleanup after; ok (.InvalidInstructionData,released)
 | .fail err => .fail err
 | .div => .div := by
 cases h : syscall (NGL_ErrorModel.message e) s <;>
  simp only [finish,h,bind_tc_ok,bind_tc_fail,bind_tc_div]

/-- A local cleanup frame is substituted only at its real call boundary. -/
theorem cleanup_frame {S : Type} (syscall : String → S → Result S)
 (cleanup : S → Result S) (pureCleanup : ∀ s, cleanup s=ok s) (e : E) (s : S) :
 finish syscall cleanup e s = NGL_ErrorModel.run syscall e s := by
 unfold finish NGL_ErrorModel.run
 simp only [pureCleanup,bind_tc_ok]

#print axioms string_log
#print axioms decoded_bytes
#print axioms abort_prefix
#print axioms cleanup_frame
end NIJ_FormatterPackets
