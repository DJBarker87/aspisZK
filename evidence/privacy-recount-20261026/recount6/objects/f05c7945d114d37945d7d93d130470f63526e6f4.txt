-- One focused V184 replay, on the pinned cached dependency cone.
import R1Z.PV_AL_PopLast
import R1Z.PV_CBL_VectorPopSpec
import R1Z.PV_AL_RemoveModel
import R1Z.PV_AL_MoveFacts
import R1Z.PV_AL_PopWorld
import R1Z.PV_AL_MoveMemory
import R1Z.PV_AL_MoveLast
import R1Z.PV_AL_MoveNativeValue
import R1Z.PV_AL_MoveWorld
import R1Z.ProverRwFullExternalTypes
import R1Z.ProverRwFullTypes
import R1Z.ProverRwFullExternalFuns
import R1Z.ProverRwFullFuns
import R1Z.PV_AL_MoveSelected
import R1Z.PV_AL_MoveClosure
#print axioms R1Z.PV_AL_MoveClosure.complete
#print axioms R1Z.PV_AL_MoveClosure.allocation_delta
#print axioms R1Z.PV_AL_MoveClosure.nonvacuous
