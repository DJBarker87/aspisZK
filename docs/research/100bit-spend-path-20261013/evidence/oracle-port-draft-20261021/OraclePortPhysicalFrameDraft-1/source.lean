import OraclePortCompactDraft

/-! Physical checkpoint framing and stored-byte hash comparisons. The body is
parsed here; deriving its accumulator fields from the reached ten-query state
is a separate obligation, intentionally not hidden in this framing theorem. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortPhysicalFrameDraft
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft
attribute [local instance] Classical.propDecidable

def magic : Bytes := [82,49,80,50,67,75,80,50]
def domain : Bytes := [85,78,80,82,79,86,69,68,58,82,49,58,99,104,101,99,107,112,111,105,110,116]

def Shape (ck : Bytes) : Prop :=
  ck.length = 1768 ∧ ck.take 16 = magic ++ [2,10,1,0,0,0,0,0] ∧
  canonical (slice ck 176 144) ∧ canonical (slice ck 408 1328) ∧
  ∀ j ∈ List.range 22, little (slice ck (320+4*j) 4) < 262144

/-- Stored proof and public bytes are hashed directly, not framed as a duplex
absorb. The checksum domain is exactly the frozen checkpoint domain. -/
def check (proof public ck : Bytes) : Program Bytes State Bool :=
  if Shape ck then
    .ask proof fun hp => .ask public fun hu => .ask (domain ++ ck.take 1736) fun hc =>
      .done (decide (slice ck 16 32 = bytes hp ∧ slice ck 48 32 = bytes hu ∧
        ck.drop 1736 = bytes hc))
  else .done false

/-- Two invocations model write-side binding and resume-side verification.
No independent frame list or different proof/public carrier is accepted. -/
def writeResume (proof public ck : Bytes) : Program Bytes State Bool :=
  bind (check proof public ck) fun written => bind (check proof public ck) fun resumed =>
    .done (written && resumed)

theorem check_frames (H : Bytes → State) (proof public ck : Bytes) (shape : Shape ck) :
    ((eval H (check proof public ck)).1.map Prod.fst) =
      [proof,public,domain ++ ck.take 1736] := by
  simp only [check,if_pos shape,eval,List.map_cons,List.map_nil]

theorem check_binding (H : Bytes → State) (proof public ck : Bytes)
    (accepted : (eval H (check proof public ck)).2 = true) :
    Shape ck ∧ slice ck 16 32 = bytes (H proof) ∧
      slice ck 48 32 = bytes (H public) ∧
      ck.drop 1736 = bytes (H (domain ++ ck.take 1736)) := by
  unfold check at accepted
  split at accepted
  · rename_i shape
    exact ⟨shape,of_decide_eq_true accepted⟩
  · contradiction

theorem six_frames (H : Bytes → State) (proof public ck : Bytes) (shape : Shape ck) :
    (eval H (writeResume proof public ck)).1.length = 6 := by
  have h := congrArg List.length (check_frames H proof public ck shape)
  simp only [List.length_map,List.length_cons,List.length_nil] at h
  simp only [writeResume,eval_bind,eval,List.length_append,List.length_nil,h]

theorem resumed_binding (H : Bytes → State) (proof public ck : Bytes)
    (accepted : (eval H (writeResume proof public ck)).2 = true) :
    Shape ck ∧ slice ck 16 32 = bytes (H proof) ∧
      slice ck 48 32 = bytes (H public) ∧
      ck.drop 1736 = bytes (H (domain ++ ck.take 1736)) := by
  simp only [writeResume,eval_bind,eval,Bool.and_eq_true] at accepted
  exact check_binding H proof public ck accepted.2

#print axioms check_frames
#print axioms check_binding
#print axioms six_frames
#print axioms resumed_binding
end AspisR1.OraclePortPhysicalFrameDraft
end
