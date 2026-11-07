import NMX_S001
import NMX_S002
import NMX_S003
import NMX_S004
import NMX_S005
import NMX_S006
import NMX_S007
import NMX_S008
import NMX_S009
import NMX_S010
import NMX_Fold01
set_option autoImplicit false
noncomputable section
namespace NMX_Fold00
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps

def p010 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.readonlyAccount masterAccount pool)) (fun _unit =>
  NMX_Fold01.p011 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint)
def v010 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Final :=
  tryThen (r1_pool_adapter.owned.require_readonly_account ops masterAccount pool) (fun value => (fun value =>
  NMX_Fold01.v011 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) value)
theorem e010 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_ValueLink.erase (eval (source ops owners) (p010 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) ()) =
 v010 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint := by
 unfold p010 v010
 rw [NMX_S010.step ops owners pool masterAccount]
 simp only [NMX_Fold01.e011] <;> rfl
#print axioms e010

def p009 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.checkpointGuard verifierCheckpoint verifier false)) (fun _unit =>
  NMX_Fold00.p010 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint)
def v009 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Final :=
  tryThen (r1_pool_adapter.owned.require_verifier_checkpoint ops verifierCheckpoint verifier false) (fun value => (fun value =>
  NMX_Fold00.v010 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) value)
theorem e009 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_ValueLink.erase (eval (source ops owners) (p009 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) ()) =
 v009 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint := by
 unfold p009 v009
 rw [NMX_S009.step ops owners verifier verifierCheckpoint]
 simp only [NMX_Fold00.e010] <;> rfl
#print axioms e009

def p008 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.readonlyBuffer proof)) (fun _unit =>
  NMX_Fold00.p009 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint)
def v008 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Final :=
  tryThen (r1_pool_adapter.owned.require_readonly_buffer proof) (fun value => (fun value =>
  NMX_Fold00.v009 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) value)
theorem e008 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_ValueLink.erase (eval (source ops owners) (p008 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) ()) =
 v008 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint := by
 unfold p008 v008
 rw [NMX_S008.step ops owners proof]
 simp only [NMX_Fold00.e009] <;> rfl
#print axioms e008

def p007 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (Slice.index_usize accounts 6#usize)) (fun verifierCheckpoint =>
  NMX_Fold00.p008 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint)
def v007 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) : Final :=
  ((Slice.index_usize accounts 6#usize)) >>= fun value => (fun verifierCheckpoint =>
  NMX_Fold00.v008 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) value
theorem e007 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) :
 NMX_ValueLink.erase (eval (source ops owners) (p007 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount) ()) =
 v007 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount := by
 unfold p007 v007
 rw [NMX_S007.step ops owners accounts]
 simp only [NMX_Fold00.e008] <;> rfl
#print axioms e007

def p006 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (Slice.index_usize accounts 5#usize)) (fun entryAccount =>
  NMX_Fold00.p007 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount)
def v006 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) : Final :=
  ((Slice.index_usize accounts 5#usize)) >>= fun value => (fun entryAccount =>
  NMX_Fold00.v007 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount) value
theorem e006 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) :
 NMX_ValueLink.erase (eval (source ops owners) (p006 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount) ()) =
 v006 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount := by
 unfold p006 v006
 rw [NMX_S006.step ops owners accounts]
 simp only [NMX_Fold00.e007] <;> rfl
#print axioms e006

def p005 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (Slice.index_usize accounts 4#usize)) (fun registryAccount =>
  NMX_Fold00.p006 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount)
def v005 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) : Final :=
  ((Slice.index_usize accounts 4#usize)) >>= fun value => (fun registryAccount =>
  NMX_Fold00.v006 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount) value
theorem e005 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) :
 NMX_ValueLink.erase (eval (source ops owners) (p005 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount) ()) =
 v005 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount := by
 unfold p005 v005
 rw [NMX_S005.step ops owners accounts]
 simp only [NMX_Fold00.e006] <;> rfl
#print axioms e005

def p004 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (Slice.index_usize accounts 3#usize)) (fun laneAccount =>
  NMX_Fold00.p005 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount)
def v004 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) : Final :=
  ((Slice.index_usize accounts 3#usize)) >>= fun value => (fun laneAccount =>
  NMX_Fold00.v005 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount) value
theorem e004 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) :
 NMX_ValueLink.erase (eval (source ops owners) (p004 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount) ()) =
 v004 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount := by
 unfold p004 v004
 rw [NMX_S004.step ops owners accounts]
 simp only [NMX_Fold00.e005] <;> rfl
#print axioms e004

def p003 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (Slice.index_usize accounts 2#usize)) (fun checkpointAccount =>
  NMX_Fold00.p004 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount)
def v003 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) : Final :=
  ((Slice.index_usize accounts 2#usize)) >>= fun value => (fun checkpointAccount =>
  NMX_Fold00.v004 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount) value
theorem e003 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) :
 NMX_ValueLink.erase (eval (source ops owners) (p003 owners ops verifier accounts pool outputLane slot proof masterAccount) ()) =
 v003 owners ops verifier accounts pool outputLane slot proof masterAccount := by
 unfold p003 v003
 rw [NMX_S003.step ops owners accounts]
 simp only [NMX_Fold00.e004] <;> rfl
#print axioms e003

def p002 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (Slice.index_usize accounts 1#usize)) (fun masterAccount =>
  NMX_Fold00.p003 owners ops verifier accounts pool outputLane slot proof masterAccount)
def v002 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) : Final :=
  ((Slice.index_usize accounts 1#usize)) >>= fun value => (fun masterAccount =>
  NMX_Fold00.v003 owners ops verifier accounts pool outputLane slot proof masterAccount) value
theorem e002 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) :
 NMX_ValueLink.erase (eval (source ops owners) (p002 owners ops verifier accounts pool outputLane slot proof) ()) =
 v002 owners ops verifier accounts pool outputLane slot proof := by
 unfold p002 v002
 rw [NMX_S002.step ops owners accounts]
 simp only [NMX_Fold00.e003] <;> rfl
#print axioms e002

def p001 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (Slice.index_usize accounts 0#usize)) (fun proof =>
  NMX_Fold00.p002 owners ops verifier accounts pool outputLane slot proof)
def v001 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) : Final :=
  ((Slice.index_usize accounts 0#usize)) >>= fun value => (fun proof =>
  NMX_Fold00.v002 owners ops verifier accounts pool outputLane slot proof) value
theorem e001 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) :
 NMX_ValueLink.erase (eval (source ops owners) (p001 owners ops verifier accounts pool outputLane slot) ()) =
 v001 owners ops verifier accounts pool outputLane slot := by
 unfold p001 v001
 rw [NMX_S001.step ops owners accounts]
 simp only [NMX_Fold00.e002] <;> rfl
#print axioms e001
end NMX_Fold00
end
