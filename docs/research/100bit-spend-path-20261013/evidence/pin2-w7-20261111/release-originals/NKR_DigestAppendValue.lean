import NKR_DigestReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestAppendValue
open Aeneas Aeneas.Std Result
open FIv_NativeValue (decode K)
open NKI_InitialPrefix (Public Openings Selectors)

def low0 (s : Selectors) : K := FIv_NativeArray.value s.low 0
def low12 (s : Selectors) : K := FIv_NativeArray.value s.low 12

theorem increment (p : Public) (o : Openings) (s : Selectors) (i : Fin 20)
 (packet : NKI_LevelsChildren.Family p.transition.live_snapshot.next_pair_index
  p.transition.live_snapshot.frontier o.z s.high) (k : Fin 8) :
 FIy_FrontierMeaning.increment p.transition.live_snapshot s o.z i.val k.val=
 (if NKI_AppendPacket.emptySide p.transition.live_snapshot.next_pair_index (NJX_AppendDomains.level i)
  then low0 s else low12 s)*NKI_AppendMeaning.residual (packet i) k := by
 have hv : decode (NJX_AppendDomains.high s.high i)=FIv_NativeArray.value s.high (34+i.val) := NKR_DigestReads.cell _ _
 have hz := NKI_AppendBits.source p.transition.live_snapshot.next_pair_index (NJX_AppendDomains.level i)
 have hz0 : NKI_AppendPacket.emptySide p.transition.live_snapshot.next_pair_index (NJX_AppendDomains.level i)=
  decide (FIy_FrontierMeaning.zero p.transition.live_snapshot i.val) := hz
 have row0d : ((34+i.val)*16)/16=34+i.val := by omega
 have row0m : ((34+i.val)*16)%16=0 := by omega
 have row12d : ((34+i.val)*16+12)/16=34+i.val := by omega
 have row12m : ((34+i.val)*16+12)%16=12 := by omega
 rw [NKR_DigestReads.residual]
 by_cases zero : FIy_FrontierMeaning.zero p.transition.live_snapshot i.val
 · have side : NKI_AppendPacket.emptySide p.transition.live_snapshot.next_pair_index (NJX_AppendDomains.level i)=true := by rw [hz0];simp only [zero,decide_true]
   have ec := (packet i).expected_call
   rw [side] at ec
   simp only [if_true] at ec
   have re := FIy_EmptyRoot.value (NJX_AppendDomains.level i) (packet i).expected ec
   have expected : FIy_FrontierMeaning.roots i.val=(packet i).expected := by
    unfold FIy_FrontierMeaning.roots
    have slot:=re.1
    simp only [NJX_AppendDomains.level_value] at slot
    rw [slot] <;> rfl
   rw [side]
   simp only [if_true,NKI_AppendPacket.start]
   simp only [FIy_FrontierMeaning.increment,if_pos zero,FIy_FrontierMeaning.rowValue,row0d,row0m,
    FIy_DigestLane.increment,expected,show (8#usize).val=8 from rfl,hv,low0]
   ring
 · have side : NKI_AppendPacket.emptySide p.transition.live_snapshot.next_pair_index (NJX_AppendDomains.level i)=false := by rw [hz0];simp only [zero,decide_false]
   have ec := (packet i).expected_call
   rw [side] at ec
   simp only [Bool.false_eq_true,if_false] at ec
   have expected : FIy_FrontierMeaning.frontier p.transition.live_snapshot i.val=(packet i).expected := by
    rw [←Result.ok.inj ec]
    unfold FIy_FrontierMeaning.frontier NJX_AppendDomains.frontier NJB_ArrayCarrier.cell
    rw [List.getElem?_eq_getElem (by rw [p.transition.live_snapshot.frontier.property];exact i.isLt)]
    rfl
   rw [side]
   simp only [Bool.false_eq_true,if_false,NKI_AppendPacket.start]
   simp only [FIy_FrontierMeaning.increment,if_neg zero,FIy_FrontierMeaning.rowValue,row12d,row12m,
    FIy_DigestLane.increment,expected,show (0#usize).val=0 from rfl,Nat.zero_add,hv,low12]
   ring

/-- One frontier key equals the two disjoint optimized local0/local12
channels. This is the arbitrary-level lemma used by finite20induction. -/
theorem packed (p : Public) (o : Openings) (s : Selectors) (i : Fin 20)
 (packets : NKI_LevelsChildren.Family p.transition.live_snapshot.next_pair_index
  p.transition.live_snapshot.frontier o.z s.high) (g : Fin 2) :
 NJB_PackLinearity.pack (fun k=>FIy_FrontierMeaning.increment p.transition.live_snapshot s o.z i.val (NJX_DigestGroups.index g k).val)=
 low0 s*decode (NKI_AppendPacket.output (packets i) ⟨g.val,by have h:=g.isLt;omega⟩)+
 low12 s*decode (NKI_AppendPacket.output (packets i) ⟨2+g.val,by have h:=g.isLt;omega⟩) := by
 have inc : (fun k=>FIy_FrontierMeaning.increment p.transition.live_snapshot s o.z i.val (NJX_DigestGroups.index g k).val)=
  (fun k=>(if NKI_AppendPacket.emptySide p.transition.live_snapshot.next_pair_index (NJX_AppendDomains.level i) then low0 s else low12 s)*
   NKI_AppendMeaning.residual (packets i) (NJX_DigestGroups.index g k)) := funext (fun k=>increment p o s i packets _)
 rw [inc,NJB_PackLinearity.scale,NKI_AppendMeaning.source,NKI_AppendMeaning.source]
 unfold NKI_AppendMeaning.contribution NKI_AppendMeaning.channel NKI_AppendMeaning.group
 cases side : NKI_AppendPacket.emptySide p.transition.live_snapshot.next_pair_index (NJX_AppendDomains.level i) <;>
  fin_cases g <;>
  simp [side,NJB_PackLinearity.zero]
#print axioms increment
#print axioms packed
end AspisR1.NKR_DigestAppendValue
end
