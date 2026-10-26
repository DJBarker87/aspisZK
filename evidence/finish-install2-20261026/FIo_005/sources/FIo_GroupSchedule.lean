import FIo_GroupModel
import FIn_ExtractInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_GroupSchedule
open Aeneas Aeneas.Std Result AspisR1Stage2.Stage2Finish
open FIo_GroupModel
theorem subset (ops : Ops) (low : Array E 16#usize) (mask : U16) :
    FIo_PairExtract.FIo_reference.subset ops low mask =
      (do let w ← ops.zero; subsetGo ops low mask [(0#usize,0#u32),(1#usize,1#u32),(2#usize,2#u32),(3#usize,3#u32),(4#usize,4#u32),(5#usize,5#u32),(6#usize,6#u32),(7#usize,7#u32),(8#usize,8#u32),(9#usize,9#u32),(10#usize,10#u32),(11#usize,11#u32),(12#usize,12#u32),(13#usize,13#u32),(14#usize,14#u32),(15#usize,15#u32)] w) := by
  simp only [FIo_PairExtract.FIo_reference.subset,subsetGo,bind_tc_ok,FIn_ExtractInstall.bind_ok]

#print axioms subset
end AspisR1.FIo_GroupSchedule
end
