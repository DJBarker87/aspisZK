import NDO_JGm_TX2_View
import Port4B_Install
import Port4B_VerifyInstall
import Port3_NativeBatchBody
import MultiproofConePhysicalAddress
import MultiproofConePhysicalDigest
import MultiproofConeRead32
import MultiproofConeSlices
import NDO_JFp_SHADigest
import F3U_Oracle
import OracleDecisionMultiTree
import RPt_JFq_Range
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_G_JGc_TX2_RealLeaves
def dictionary {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) :
    AspisR1Stage2.aspis_core.digest.Digest32 Hash :=
  {D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}

end AspisR1.JGy_G_JGc_TX2_RealLeaves
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_G_JGc_TX2_LeafHelpers
open Aeneas Aeneas.Std Result

theorem four {A : Type} (xs c0 c1 c2 c3 : List A) (length : xs.length=128)
    (h0 : (xs.drop 0).take 32=c0) (h1 : (xs.drop 32).take 32=c1)
    (h2 : (xs.drop 64).take 32=c2) (h3 : (xs.drop 96).take 32=c3) :
    xs=c0++c1++c2++c3 := by
  have split : xs.take 128=(xs.take 32)++(xs.drop 32).take 32++
      (xs.drop 64).take 32++(xs.drop 96).take 32 := by
    rw [List.take_add (i:=32) (j:=96),List.take_add (i:=32) (j:=64),List.take_add (i:=32) (j:=32)]
    simp only [List.drop_drop,List.append_assoc]
  have h0' : xs.take 32=c0 := by simpa only [List.drop_zero] using h0
  rw [List.take_of_length_le (by omega),h0',h1,h2,h3] at split
  exact split
#print axioms four
end AspisR1.JGy_G_JGc_TX2_LeafHelpers
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_G_JGh_TX2_NodeViews
open Aeneas Aeneas.Std Result
@[irreducible] def readCell (nodes : Slice U8) (cursor : Nat) : AspisV8R19.SourceDuplexStep.State :=
  fun i => AspisV8R19.SqueezeOracleBridge.decodeByte
    (((nodes.val.drop (32*cursor)).take 32).getD i.val 0#u8)

theorem read_selected (nodes : Slice U8) (cursor : Nat) (a : Array U8 32#usize)
    (selected : (nodes.val.drop (32*cursor)).take 32=a.val) :
    readCell nodes cursor=AspisV8R19.SqueezeOracleBridge.decodeState a := by
  unfold readCell
  rw [selected]
  funext i
  rw [List.getD_eq_getElem _ _ (show i.val<a.val.length by rw [a.property];exact i.isLt)]
  rfl
#print axioms read_selected
end AspisR1.JGy_G_JGh_TX2_NodeViews
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_G_JGk_TX2_ScratchIndices
open Aeneas Aeneas.Std Result
theorem snoc_set {α : Type} (xs : List α) (i : Nat) (x : α) (bound : i<xs.length) :
    (xs.set i x).take (i+1)=xs.take i++[x] := by
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_set] using bound),List.take_set]
  rw [List.set_eq_of_length_le (by simp only [List.length_take];omega)]
  simp only [List.getElem_set_self]
#print axioms snoc_set
end AspisR1.JGy_G_JGk_TX2_ScratchIndices
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_G_JGk_TX2_ParentWrite
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

def parentIndex (index : U32) : U32 := UScalar.ofNat (index.val/2) (by scalar_tac)
def next (w : Usize) (room : w.val<16) : Usize := UScalar.ofNat (w.val+1) (by scalar_tac)
def after (s : reference.Scratch) (index : U32) (w : Usize) (value : Array U8 32#usize)
    (cursor : Usize) : reference.Scratch :=
  {s with idx:=s.idx.set w (parentIndex index),val:=s.val.set w value,«at»:=cursor}

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (left right out : State) (ni cursor : Usize) (index : U32) (w : Usize)
    (room : w.val<16)
    (hashed : JFp_SHADigest.digest (BinMerkle32Path.nodeInput (OracleDecisionMultiTree.children left right))=out) :
    reference.write_parent (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s (encodeState left) (encodeState right) ni cursor index w=
      ok (.Next (after s index w (encodeState out) cursor) ni (next w room)) := by
  let D' := Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)
  have total : MultiproofConeNodeDomain.HashTotal D' hash := by
    intro input
    exact ⟨encodeState (JFp_SHADigest.digest (flatten input)),rfl⟩
  have call : D'.digest hash (MultiproofConePhysicalDigest.parts (encodeState left) (encodeState right))=
      ok (encodeState out) := by
    change ok (encodeState (JFp_SHADigest.digest (flatten
      (MultiproofConePhysicalDigest.parts (encodeState left) (encodeState right)))))=_
    rw [MultiproofConePhysicalAddress.parent_address,state_roundtrip,state_roundtrip,hashed]
  obtain ⟨returned,run,post⟩ := WP.spec_imp_exists
    (MultiproofConePhysicalDigest.write_observed D' hash total s (encodeState left) (encodeState right)
      ni cursor index w room)
  obtain ⟨value,parent,nw,observed,parentVal,nextVal,state⟩ := post
  have valueEq : value=encodeState out := Result.ok.inj (observed.symm.trans call)
  have parentEq : parent=parentIndex index := UScalar.eq_of_val_eq parentVal
  have nextEq : nw=next w room := UScalar.eq_of_val_eq nextVal
  rw [valueEq,parentEq,nextEq] at state
  exact run.trans (congrArg ok state)
#print axioms source
end AspisR1.JGy_G_JGk_TX2_ParentWrite
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_G_JGm_TX2_BinarySelect
open Aeneas Aeneas.Std Result MultiproofConeRef

theorem pair {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (nodes : Slice U8) (i w ni ni2 : Usize)
    (index : U32) (left right : Array U8 32#usize)
    (ri : Array.index_usize s.idx i=ok index)
    (rv : Array.index_usize s.val i=ok left)
    (inc : i+1#usize=ok ni) (more : ni<s.n)
    (rn : Array.index_usize s.idx ni=ok (index ^^^ 1#u32))
    (rr : Array.index_usize s.val ni=ok right)
    (inc2 : i+2#usize=ok ni2) :
    reference.binary_step D hash s nodes i w=
      reference.write_parent D hash s left right ni2 s.«at» index w := by
  simp only [reference.binary_step,ri,rv,inc,bind_tc_ok,if_pos more,rn,lift,if_true,rr,inc2]
#print axioms pair

/-- Only the input reads and the pure occupied-pair test are simplified here.
The external path still executes its actual range/read32/cursor operations. -/
theorem external {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (nodes : Slice U8) (i w ni : Usize)
    (index : U32) (value : Array U8 32#usize)
    (ri : Array.index_usize s.idx i=ok index)
    (rv : Array.index_usize s.val i=ok value)
    (inc : i+1#usize=ok ni)
    (unpaired : ∀ h : ni<s.n, ∃ other, Array.index_usize s.idx ni=ok other ∧ other≠index ^^^ 1#u32) :
    reference.binary_step D hash s nodes i w=
      (do let remaining ← Slice.len nodes-s.«at»
          if remaining<32#usize then ok (.Stop s)
          else
            let cursor ← s.«at»+32#usize
            let view ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
              nodes {start:=s.«at»,«end»:=cursor}
            let sibling ← reference.read32 view
            if index &&& 1#u32=0#u32 then
              reference.write_parent D hash s value sibling ni cursor index w
            else reference.write_parent D hash s sibling value ni cursor index w) := by
  simp only [reference.binary_step,ri,rv,inc,bind_tc_ok]
  by_cases more : ni<s.n
  · obtain ⟨other,read,ne⟩ := unpaired more
    simp only [if_pos more,read,bind_tc_ok,lift,if_neg ne]
  · simp only [if_neg more,lift,bind_tc_ok]
#print axioms external
end AspisR1.JGy_G_JGm_TX2_BinarySelect
end

set_option autoImplicit false
namespace AspisR1.JGy_G_JGm_TX2_Scalar
open Aeneas Aeneas.Std Result

theorem add (x y z : Usize) (sum : z.val=x.val+y.val) : x+y=ok z := by
  obtain ⟨v,run,value⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=x) (y:=y) (by scalar_tac))
  have same : v=z := UScalar.eq_of_val_eq (by omega)
  simpa only [same] using run
#print axioms add

theorem sub (x y z : Usize) (order : y.val≤x.val) (diff : z.val=x.val-y.val) : x-y=ok z := by
  obtain ⟨v,run,value⟩ := WP.spec_imp_exists (UScalar.sub_spec (x:=x) (y:=y) (by scalar_tac))
  have same : v=z := UScalar.eq_of_val_eq (by omega)
  simpa only [same] using run
#print axioms sub
end AspisR1.JGy_G_JGm_TX2_Scalar

set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_G_JGm_TX2_ReadCell
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem source (nodes : Slice U8) (cell : Nat) (start finish : Usize)
    (hs : start.val=32*cell) (hf : finish.val=32*cell+32)
    (bound : finish.val≤nodes.val.length) :
    reference.read32 (MultiproofConeSlices.sub nodes start finish)=
      ok (encodeState (JGy_G_JGh_TX2_NodeViews.readCell nodes cell)) := by
  have order : start.val≤finish.val := by omega
  have len : (MultiproofConeSlices.sub nodes start finish).val.length=32 := by
    rw [MultiproofConeSlices.sub_length nodes start finish order bound];omega
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub nodes start finish) (by omega)
  have selected : (nodes.val.drop (32*cell)).take 32=chunk.val := by
    rw [List.take_of_length_le (by omega)] at bytes
    simpa only [MultiproofConeSlices.sub,hs,hf,Nat.add_sub_cancel_left] using bytes.symm
  have decoded := JGy_G_JGh_TX2_NodeViews.read_selected nodes cell chunk selected
  rw [decoded,array_roundtrip]
  exact run
#print axioms source
end AspisR1.JGy_G_JGm_TX2_ReadCell
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_G_JGm_TX2_Supplied
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge

def leading (nodes : Slice U8) (finish : Usize) : Slice U8 := MultiproofConeSlices.sub nodes 0#usize finish

theorem size (nodes : Slice U8) (finish : Usize) (bound : finish.val≤nodes.val.length) :
    (leading nodes finish).val.length=finish.val := by
  simpa only [leading,show (0#usize).val=0 from rfl,Nat.sub_zero] using MultiproofConeSlices.sub_length nodes 0#usize finish (by change (0:Nat)≤finish.val;omega) bound
#print axioms size

theorem sub_prefix (nodes : Slice U8) (limit start finish : Usize)
    (order : start.val≤finish.val) (bound : finish.val≤limit.val) :
    MultiproofConeSlices.sub (leading nodes limit) start finish=MultiproofConeSlices.sub nodes start finish := by
  apply Subtype.ext
  simp only [MultiproofConeSlices.sub,leading,show (0#usize).val=0 from rfl,List.drop_zero,Nat.sub_zero]
  simpa only [List.drop_zero,Nat.zero_add] using JFq_Range.nested nodes.val 0 limit.val start.val (finish.val-start.val) (by omega)
#print axioms sub_prefix

theorem source (nodes : Slice U8) (cell : Nat) (limit start finish : Usize)
    (hs : start.val=32*cell) (hf : finish.val=32*cell+32)
    (bound : finish.val≤limit.val) (fits : limit.val≤nodes.val.length) :
    reference.read32 (MultiproofConeSlices.sub (leading nodes limit) start finish)=
      ok (encodeState (JGy_G_JGh_TX2_NodeViews.readCell nodes cell)) := by
  rw [sub_prefix nodes limit start finish (by omega) bound]
  exact JGy_G_JGm_TX2_ReadCell.source nodes cell start finish hs hf (by omega)
#print axioms source

end AspisR1.JGy_G_JGm_TX2_Supplied
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_G_JGm_TX2_ExternalRun
open Aeneas Aeneas.Std Result MultiproofConeRef

theorem source {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (nodes : Slice U8) (i w ni cursor remaining : Usize)
    (index : U32) (value sibling : Array U8 32#usize)
    (ri : Array.index_usize s.idx i=ok index)
    (rv : Array.index_usize s.val i=ok value)
    (inc : i+1#usize=ok ni)
    (unpaired : ∀ h : ni<s.n, ∃ other, Array.index_usize s.idx ni=ok other ∧ other≠index ^^^ 1#u32)
    (sub : Slice.len nodes-s.«at»=ok remaining) (room : ¬remaining<32#usize)
    (advance : s.«at»+32#usize=ok cursor)
    (order : s.«at».val≤cursor.val) (bound : cursor.val≤nodes.val.length)
    (read : reference.read32 (MultiproofConeSlices.sub nodes s.«at» cursor)=ok sibling) :
    reference.binary_step D hash s nodes i w=
      if index &&& 1#u32=0#u32 then
        reference.write_parent D hash s value sibling ni cursor index w
      else reference.write_parent D hash s sibling value ni cursor index w := by
  rw [JGy_G_JGm_TX2_BinarySelect.external D hash s nodes i w ni index value ri rv inc unpaired]
  simp only [sub,bind_tc_ok,if_neg room,advance,MultiproofConeSlices.range_total nodes s.«at» cursor order bound,read]
#print axioms source
end AspisR1.JGy_G_JGm_TX2_ExternalRun
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_G_JGm_TX2_RowControl
open Aeneas Aeneas.Std Result MultiproofConeRef

theorem step {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s t : reference.Scratch) (nodes : Slice U8) (i w ni nw : Usize)
    (active : i<s.n)
    (run : reference.binary_step D hash s nodes i w=ok (.Next t ni nw)) :
    reference.level_rows D hash s nodes i w=reference.level_rows D hash t nodes ni nw := by
  rw [reference.level_rows,if_neg (by change ¬i.val≥s.n.val; change i.val<s.n.val at active;omega),run]
  rfl
#print axioms step

theorem done {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (nodes : Slice U8) (i w : Usize) (finished : s.n ≤ i) :
    reference.level_rows D hash s nodes i w=ok (.Done {s with n:=w}) := by
  rw [reference.level_rows,if_pos finished]
#print axioms done
end AspisR1.JGy_G_JGm_TX2_RowControl
end

set_option autoImplicit false
namespace AspisR1.JGy_G_JGk_TX2_ZeroWindows
open Aeneas Aeneas.Std

theorem source (n : Nat) (xs : List U8) (size : xs.length=32*n)
    (windows : ∀ i,i<n → (xs.drop (32*i)).take 32=List.replicate 32 0#u8) :
    xs=List.replicate (32*n) 0#u8 := by
  induction n generalizing xs with
  | zero =>
    have h : xs=[] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    rfl
  | succ n ih =>
    have head : xs.take 32=List.replicate 32 0#u8 := by
      simpa only [Nat.mul_zero,List.drop_zero] using windows 0 (by omega)
    have tail : xs.drop 32=List.replicate (32*n) 0#u8 := by
      apply ih
      · simp only [List.length_drop]
        omega
      · intro i hi
        have h := windows (i+1) (by omega)
        simpa only [List.drop_drop,show 32+32*i=32*(i+1) from by omega] using h
    calc
      xs=xs.take 32++xs.drop 32 := (List.take_append_drop 32 xs).symm
      _=List.replicate 32 0#u8++List.replicate (32*n) 0#u8 := by rw [head,tail]
      _=List.replicate (32*(n+1)) 0#u8 := by
        rw [←List.replicate_add]
        congr 1
        omega
#print axioms source
end AspisR1.JGy_G_JGk_TX2_ZeroWindows
