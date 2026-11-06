import NKK_RawPrefix
import NKK_LogAlgebra
import NKK_LogReduce
set_option autoImplicit false
noncomputable section
namespace NKK_QueryStage
open Aeneas Aeneas.Std Result NKK_NativeRaw
open AspisR1 NID_ResumeEmission NJU_ResumeObserved

def source8 (r : Reader) : NJU_Log.Run Event (List U32 × Reader) := do
 let (b0,r1) ← recordRaw 4#usize r
 let (b1,r2) ← recordRaw 4#usize r1
 let (b2,r3) ← recordRaw 4#usize r2
 let (b3,r4) ← recordRaw 4#usize r3
 let (b4,r5) ← recordRaw 4#usize r4
 let (b5,r6) ← recordRaw 4#usize r5
 let (b6,r7) ← recordRaw 4#usize r6
 let (b7,r8) ← recordRaw 4#usize r7
 pure ([core.num.U32.from_le_bytes b0,core.num.U32.from_le_bytes b1,core.num.U32.from_le_bytes b2,core.num.U32.from_le_bytes b3,core.num.U32.from_le_bytes b4,core.num.U32.from_le_bytes b5,core.num.U32.from_le_bytes b6,core.num.U32.from_le_bytes b7],r8)

def model8 (r : Reader) : NJU_Log.Run Event (List U32 × Reader) := do
 let (bs,next) ← NKK_RawPrefix.literal 4#usize 8 r
 pure (bs.map core.num.U32.from_le_bytes,next)

theorem stage8 (r : Reader) : model8 r=source8 r := by
 unfold model8 source8
 simp only [NKK_RawPrefix.literal,NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,
  List.map_cons,List.map_nil,NJU_Log.prod_cases]

#print axioms stage8

def source6 (r : Reader) : NJU_Log.Run Event (List U32 × Reader) := do
 let (b0,r1) ← recordRaw 4#usize r
 let (b1,r2) ← recordRaw 4#usize r1
 let (b2,r3) ← recordRaw 4#usize r2
 let (b3,r4) ← recordRaw 4#usize r3
 let (b4,r5) ← recordRaw 4#usize r4
 let (b5,r6) ← recordRaw 4#usize r5
 pure ([core.num.U32.from_le_bytes b0,core.num.U32.from_le_bytes b1,core.num.U32.from_le_bytes b2,core.num.U32.from_le_bytes b3,core.num.U32.from_le_bytes b4,core.num.U32.from_le_bytes b5],r6)

def model6 (r : Reader) : NJU_Log.Run Event (List U32 × Reader) := do
 let (bs,next) ← NKK_RawPrefix.literal 4#usize 6 r
 pure (bs.map core.num.U32.from_le_bytes,next)

theorem stage6 (r : Reader) : model6 r=source6 r := by
 unfold model6 source6
 simp only [NKK_RawPrefix.literal,NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,
  List.map_cons,List.map_nil,NJU_Log.prod_cases]

#print axioms stage6
end NKK_QueryStage
