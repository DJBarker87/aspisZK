import R1Z.PV_OWNB_Cursor
set_option autoImplicit false
namespace R1Z.PV_OWNB_ActualSink
open PV_OWNB_Cursor PV_OWN_Heap PV_OWN_Bytes PV_OWN_Link
/-- Copies whatever padding the runtime produces. Active bytes must represent v. -/
def sink (q : Cursor) (v : Link) (actual : Bytes) : Cursor :=
 let c:=store q.cell (q.written*8) 8 actual
 {q with
  cell:=c
  written:=q.written+1
  memory:={q.memory with heap:=put q.memory.heap q.token.address (some c)}
  output:=fun i=>if i=q.written then v else q.output i}

theorem ownership (q : Cursor) (v : Link) (actual : Bytes) (h:Valid q) :
 Writable (sink q v actual).memory q.owner q.token (sink q v actual).cell := by
 unfold Valid at h
 unfold sink
 exact ⟨⟨⟨put_same _ _ _,h.1.1.1.2.1,h.1.1.1.2.2⟩,h.1.1.2.1,h.1.1.2.2⟩,h.1.2⟩

theorem generation (q : Cursor) (v : Link) (actual : Bytes) :
 (sink q v actual).memory.generations=q.memory.generations ∧ (sink q v actual).token=q.token :=
 ⟨rfl,rfl⟩
attribute [local irreducible] sink
#print axioms ownership
#print axioms generation
end R1Z.PV_OWNB_ActualSink
