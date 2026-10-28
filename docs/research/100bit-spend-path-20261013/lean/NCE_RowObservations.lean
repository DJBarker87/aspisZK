import NCE_CarrierEffects
import NBJ_NodeObservation

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCE_RowObservations
open Aeneas Aeneas.Std Result MultiproofConeRef NCE_OpeningCuts NCE_CarrierEffects
open MultiproofConeNodeDomain
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- One occupied native row: the existing physical request/reply/store law
is consumed at the SAME actual caller. The returned digest is written before
any next row, and the arbitrary old log is retained without a clock bound. -/
theorem paired (H : Bytes → State) (native : Node) (cut : NCE_Native_Row H native)
    (caller : Carrier) (physical : Slice U8) (i w : Usize)
    (size : physical.val.length ≤ 5504) (domain : RowDomain physical caller.scratch i w)
    (active : i.val < caller.scratch.n.val)
    (both : i.val+1 < caller.scratch.n.val ∧
      caller.scratch.idx.val[i.val+1]! = caller.scratch.idx.val[i.val]! ^^^ 1#u32) :
    ∃ next parent nw,
      next.val = i.val+2 ∧ parent.val = caller.scratch.idx.val[i.val]!.val/2 ∧ nw.val = w.val+1 ∧
      let input := MultiproofConePhysicalDigest.parts caller.scratch.val.val[i.val]! caller.scratch.val.val[i.val+1]!
      let after := {caller.scratch with idx:=caller.scratch.idx.set w parent, val:=caller.scratch.val.set w (encodeState (H (flatten input)))}
      eval H (native caller physical i w) =
        ([(flatten input,H (flatten input))],
          (ok (.Next after next nw),{caller with scratch:=after,log:=caller.log++[(flatten input,H (flatten input))]})) := by
  obtain ⟨next,parent,nw,nv,pv,wv,observed⟩ :=
    NBJ_NodeObservation.paired_observation H physical caller.scratch i w domain active both
  refine ⟨next,parent,nw,nv,pv,wv,?_⟩
  rw [cut caller physical i w size domain active,annotate_eval,observed]
  rfl

/-- Short native rejection issues no digest request and retains the actual
caller. No independently chosen failed scratch or empty prefix is assumed. -/
theorem short (H : Bytes → State) (native : Node) (cut : NCE_Native_Row H native)
    (caller : Carrier) (physical : Slice U8) (i w : Usize)
    (size : physical.val.length ≤ 5504) (domain : RowDomain physical caller.scratch i w)
    (active : i.val < caller.scratch.n.val)
    (unpaired : ¬(i.val+1 < caller.scratch.n.val ∧
      caller.scratch.idx.val[i.val+1]! = caller.scratch.idx.val[i.val]! ^^^ 1#u32))
    (missing : physical.val.length-caller.scratch.«at».val < 32) :
    eval H (native caller physical i w) = ([],(ok (.Stop caller.scratch),caller)) := by
  rw [cut caller physical i w size domain active,annotate_eval,
    NBJ_NodeObservation.short_observation H physical caller.scratch i w domain active unpaired missing]
  simp only [rowScratch,List.append_nil]

/-- One supplied-sibling native row: exact selected physical chunk, parity,
request, returned reply, cursor and byte write on the SAME caller carrier. -/
theorem supplied (H : Bytes → State) (native : Node) (cut : NCE_Native_Row H native)
    (caller : Carrier) (physical : Slice U8) (i w : Usize)
    (size : physical.val.length ≤ 5504) (domain : RowDomain physical caller.scratch i w)
    (active : i.val < caller.scratch.n.val)
    (unpaired : ¬(i.val+1 < caller.scratch.n.val ∧
      caller.scratch.idx.val[i.val+1]! = caller.scratch.idx.val[i.val]! ^^^ 1#u32))
    (enough : caller.scratch.«at».val+32 ≤ physical.val.length) :
    ∃ next cursor chunk parent nw,
      next.val = i.val+1 ∧ cursor.val = caller.scratch.«at».val+32 ∧
      chunk.val = (physical.val.drop caller.scratch.«at».val).take 32 ∧
      parent.val = caller.scratch.idx.val[i.val]!.val/2 ∧ nw.val = w.val+1 ∧
      let left := if caller.scratch.idx.val[i.val]! &&& 1#u32 = 0#u32 then caller.scratch.val.val[i.val]! else chunk
      let right := if caller.scratch.idx.val[i.val]! &&& 1#u32 = 0#u32 then chunk else caller.scratch.val.val[i.val]!
      let input := MultiproofConePhysicalDigest.parts left right
      let after := {caller.scratch with idx:=caller.scratch.idx.set w parent, val:=caller.scratch.val.set w (encodeState (H (flatten input))),«at»:=cursor}
      eval H (native caller physical i w) =
        ([(flatten input,H (flatten input))],
          (ok (.Next after next nw),{caller with scratch:=after,log:=caller.log++[(flatten input,H (flatten input))]})) := by
  obtain ⟨next,cursor,chunk,parent,nw,nv,cv,bytes,pv,wv,observed⟩ :=
    NBJ_NodeObservation.supplied_observation H physical caller.scratch i w domain active unpaired enough
  refine ⟨next,cursor,chunk,parent,nw,nv,cv,bytes,pv,wv,?_⟩
  rw [cut caller physical i w size domain active,annotate_eval,observed]
  rfl

#print axioms paired
#print axioms short
#print axioms supplied
end AspisR1.NCE_RowObservations
end
