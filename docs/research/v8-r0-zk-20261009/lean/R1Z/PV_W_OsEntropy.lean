import R1Z.PV_W_OsFile
set_option autoImplicit false
namespace R1Z.PV_W_OsEntropy
open PV_W_Threading PV_RunJoin_OsWorld PV_W_OsFile
variable {E File Reply Time Worker Fs Allocator Extra C : Type}

abbrev Update (E Fs Allocator Extra : Type) :=
  PV_RunJoin_CallerWorld.RawReply E → Fs → PV_W_Enriched.Process Allocator Extra →
    Fs × PV_W_Enriched.Process Allocator Extra

def afterDraw (update : Update E Fs Allocator Extra) (i : Fin 128)
    (w : Full E File Reply Time Worker Fs Allocator Extra) : Full E File Reply Time Worker Fs Allocator Extra :=
  let next := update (w.os.entropy i) w.filesystem w.process
  ⟨{w.os with entropyUsed := w.os.entropyUsed + 1},next.1,next.2⟩

/-- All replies, including partial-buffer/error replies, consume their draw.
A cursor mismatch is an interpreter fault and performs no native draw. -/
def draw (update : Update E Fs Allocator Extra)
    (tag : Fin 128 → PV_RunJoin_CallerWorld.RawReply E → C) (i : Fin 128) :
    M (Full E File Reply Time Worker Fs Allocator Extra) C Fault (PV_RunJoin_CallerWorld.RawReply E) := fun w =>
  if w.os.entropyUsed = i.val then
    ⟨.ok (w.os.entropy i),afterDraw update i w,[(w,tag i (w.os.entropy i))]⟩
  else ⟨.fail .entropyCursor,w,[]⟩

def Step (update : Update E Fs Allocator Extra)
    (tag : Fin 128 → PV_RunJoin_CallerWorld.RawReply E → C)
    (w : Full E File Reply Time Worker Fs Allocator Extra) (c : C)
    (next : Full E File Reply Time Worker Fs Allocator Extra) : Prop :=
  ∃ i : Fin 128, w.os.entropyUsed = i.val ∧ c = tag i (w.os.entropy i) ∧ next = afterDraw update i w

theorem draw_at (update : Update E Fs Allocator Extra)
    (tag : Fin 128 → PV_RunJoin_CallerWorld.RawReply E → C) (i : Fin 128)
    (w : Full E File Reply Time Worker Fs Allocator Extra) (at_cursor : w.os.entropyUsed = i.val) :
    draw update tag i w =
      ⟨.ok (w.os.entropy i),afterDraw update i w,[(w,tag i (w.os.entropy i))]⟩ := by
  simp only [draw,at_cursor,↓reduceIte]

theorem draw_rejected (update : Update E Fs Allocator Extra)
    (tag : Fin 128 → PV_RunJoin_CallerWorld.RawReply E → C) (i : Fin 128)
    (w : Full E File Reply Time Worker Fs Allocator Extra) (wrong_cursor : w.os.entropyUsed ≠ i.val) :
    draw update tag i w = ⟨.fail .entropyCursor,w,[]⟩ := by
  simp only [draw,wrong_cursor,↓reduceIte]

theorem draw_valid (update : Update E Fs Allocator Extra)
    (tag : Fin 128 → PV_RunJoin_CallerWorld.RawReply E → C) (i : Fin 128) :
    Valid (Step (File := File) (Reply := Reply) (Time := Time) (Worker := Worker) update tag) (draw update tag i) := by
  intro w
  by_cases at_cursor : w.os.entropyUsed = i.val
  · rw [draw_at update tag i w at_cursor]
    exact .cons ⟨i,at_cursor,rfl,rfl⟩ (.nil _)
  · rw [draw_rejected update tag i w at_cursor]
    exact .nil w

/-- No successful-entropy guard is present; the exact reply and its optional
native error survive, and the cursor advances in both native outcome cases. -/
theorem draw_complete_reply (update : Update E Fs Allocator Extra)
    (tag : Fin 128 → PV_RunJoin_CallerWorld.RawReply E → C) (i : Fin 128)
    (w : Full E File Reply Time Worker Fs Allocator Extra) (at_cursor : w.os.entropyUsed = i.val) :
    (draw update tag i w).outcome = .ok (w.os.entropy i) ∧
    (draw update tag i w).world.os.entropyUsed = w.os.entropyUsed + 1 := by
  rw [draw_at update tag i w at_cursor]
  exact ⟨rfl,rfl⟩

#print axioms draw_at
#print axioms draw_rejected
#print axioms draw_valid
#print axioms draw_complete_reply
end R1Z.PV_W_OsEntropy
