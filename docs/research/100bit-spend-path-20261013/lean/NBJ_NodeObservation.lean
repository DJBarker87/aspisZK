import NBJ_NodeCuts

set_option autoImplicit false
namespace AspisR1.NBJ_NodeObservation
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalProgram MultiproofConeNodeDomain MultiproofConePhysicalTransport
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps AspisV8R19.SqueezeOracleBridge

/-- Compose the occupied source cut with the existing full-coordinate writer.
The same two prestate cells determine request, reply and complete poststate. -/
theorem paired_observation (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
    (physical : Slice U8) (s : reference.Scratch) (i w : Usize)
    (domain : RowDomain physical s i w) (active : i.val < s.n.val)
    (paired : i.val+1 < s.n.val ∧ s.idx.val[i.val+1]! = s.idx.val[i.val]! ^^^ 1#u32) :
    ∃ (next : Usize) (parent : U32) (nw : Usize),
      next.val = i.val+2 ∧ parent.val = s.idx.val[i.val]!.val/2 ∧ nw.val = w.val+1 ∧
      let input := MultiproofConePhysicalDigest.parts s.val.val[i.val]! s.val.val[i.val+1]!
      eval H (transport (node s physical i w)) =
        ([(flatten input,H (flatten input))],
          ok (.Next {s with idx := s.idx.set w parent,val := s.val.set w (encodeState (H (flatten input)))} next nw)) := by
  obtain ⟨ni,next,nv,xv,eq⟩ := NBJ_NodeCuts.paired_program physical s i w domain active paired
  have dom := domain
  simp only [RowDomain] at dom
  have wb : w.val < 16 := by omega
  let input := MultiproofConePhysicalDigest.parts s.val.val[i.val]! s.val.val[i.val+1]!
  obtain ⟨parent,nw,pv,wv,finish⟩ := NBI_Frame.finish_exact s
    (encodeState (H (flatten input))) next s.«at» s.idx.val[i.val]! w wb
  refine ⟨next,parent,nw,xv,pv,wv,?_⟩
  dsimp only
  rw [eq,writer_observation]
  exact congrArg (fun result => ([(flatten input,H (flatten input))],result)) finish

/-- Short rejection has empty chronological digest log and untouched scratch. -/
theorem short_observation (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
    (physical : Slice U8) (s : reference.Scratch) (i w : Usize)
    (domain : RowDomain physical s i w) (active : i.val < s.n.val)
    (unpaired : ¬(i.val+1 < s.n.val ∧ s.idx.val[i.val+1]! = s.idx.val[i.val]! ^^^ 1#u32))
    (short : physical.val.length-s.«at».val < 32) :
    eval H (transport (node s physical i w)) = ([],ok (.Stop s)) := by
  rw [NBJ_NodeCuts.short_program physical s i w domain active unpaired short]
  rfl

/-- Full supplied-row request/reply/poststate, after physical selection on the
same carrier. Arbitrary replies are installed before the next row begins. -/
theorem supplied_observation (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
    (physical : Slice U8) (s : reference.Scratch) (i w : Usize)
    (domain : RowDomain physical s i w) (active : i.val < s.n.val)
    (unpaired : ¬(i.val+1 < s.n.val ∧ s.idx.val[i.val+1]! = s.idx.val[i.val]! ^^^ 1#u32))
    (enough : s.«at».val+32 ≤ physical.val.length) :
    ∃ (next cursor : Usize) (chunk : MultiproofConePhysicalProgram.Digest) (parent : U32) (nw : Usize),
      next.val = i.val+1 ∧ cursor.val = s.«at».val+32 ∧
      chunk.val = (physical.val.drop s.«at».val).take 32 ∧
      parent.val = s.idx.val[i.val]!.val/2 ∧ nw.val = w.val+1 ∧
      let left := if s.idx.val[i.val]! &&& 1#u32 = 0#u32 then s.val.val[i.val]! else chunk
      let right := if s.idx.val[i.val]! &&& 1#u32 = 0#u32 then chunk else s.val.val[i.val]!
      let input := MultiproofConePhysicalDigest.parts left right
      eval H (transport (node s physical i w)) =
        ([(flatten input,H (flatten input))],
          ok (.Next {s with idx := s.idx.set w parent,val := s.val.set w (encodeState (H (flatten input))),«at» := cursor} next nw)) := by
  obtain ⟨next,cursor,chunk,nv,cv,bytes,eq⟩ :=
    NBJ_NodeCuts.supplied_program physical s i w domain active unpaired enough
  let left := if s.idx.val[i.val]! &&& 1#u32 = 0#u32 then s.val.val[i.val]! else chunk
  let right := if s.idx.val[i.val]! &&& 1#u32 = 0#u32 then chunk else s.val.val[i.val]!
  let input := MultiproofConePhysicalDigest.parts left right
  have nodeEq : node s physical i w = writer s left right next cursor s.idx.val[i.val]! w := by
    rw [eq]
    by_cases parity : s.idx.val[i.val]! &&& 1#u32 = 0#u32
    · simp only [parity,if_true,left,right]
    · simp only [parity,if_false,left,right]
  have dom := domain
  simp only [RowDomain] at dom
  have wb : w.val < 16 := by omega
  obtain ⟨parent,nw,pv,wv,finish⟩ := NBI_Frame.finish_exact s
    (encodeState (H (flatten input))) next cursor s.idx.val[i.val]! w wb
  refine ⟨next,cursor,chunk,parent,nw,nv,cv,bytes,pv,wv,?_⟩
  dsimp only
  rw [nodeEq,writer_observation]
  exact congrArg (fun result => ([(flatten input,H (flatten input))],result)) finish

#print axioms paired_observation
#print axioms short_observation
#print axioms supplied_observation
end AspisR1.NBJ_NodeObservation
