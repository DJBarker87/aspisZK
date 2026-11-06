import NJQ_RegistryTotal
import NJQ_EntryTotal
import NJQ_MasterTotal
import NJQ_CheckpointTotal
import NJQ_IdentityCut
import NJQ_Carrier
set_option autoImplicit false
noncomputable section
namespace NJQ_Canonical
open Aeneas Aeneas.Std Result

def mapOuter {A B : Type} (f : A→B) : Result A→Result B
 | .ok x=>.ok (f x) | .fail e=>.fail e | .div=>.div

def registryResult (r : core.result.Result NJI_V1Carrier.R NJI_V1Carrier.F) :
 core.result.Result NJI_V1Carrier.CR NJI_V1Carrier.CF :=
 match r with | .Ok p=>.Ok (NJI_V1Carrier.registry p) | .Err e=>.Err (NJI_V1Carrier.error e)
def entryResult (r : core.result.Result NJI_V1Carrier.E NJI_V1Carrier.F) :
 core.result.Result NJI_V1Carrier.CE NJI_V1Carrier.CF :=
 match r with | .Ok p=>.Ok (NJI_V1Carrier.entry p) | .Err e=>.Err (NJI_V1Carrier.error e)

/-- Concrete natural model on the adopted carrier. This alone is not an
identification with an opaque cohort slot and earns no native row credit. -/
def registry (b : Slice U8) := mapOuter registryResult (NJQ_Registry.model b)
theorem registry_result (b : Slice U8) (log : Option NJI_V1Carrier.R) (out : core.result.Result NJI_V1Carrier.R NJI_V1Carrier.F)
 (h : NJQ_RegistryTotal.Cut b log out) : ok (registryResult out)=registry b := by
 have same:=NJQ_RegistryTotal.native_source b log out h
 rw [NJQ_Registry.source] at same
 exact congrArg (mapOuter registryResult) same
set_option pp.proofs false in
#print registry_result
#print axioms registry_result

/-- Concrete natural model on the adopted carrier. This alone is not an
identification with an opaque cohort slot and earns no native row credit. -/
def entry (b : Slice U8) := mapOuter entryResult (NJQ_Entry.model b)
theorem entry_result (b : Slice U8) (log : Option NJI_V1Carrier.E) (out : core.result.Result NJI_V1Carrier.E NJI_V1Carrier.F)
 (h : NJQ_EntryTotal.Cut b log out) : ok (entryResult out)=entry b := by
 have same:=NJQ_EntryTotal.native_source b log out h
 rw [NJQ_Entry.source] at same
 exact congrArg (mapOuter entryResult) same
set_option pp.proofs false in
#print entry_result
#print axioms entry_result

/-- Concrete natural model on the adopted carrier. This alone is not an
identification with an opaque cohort slot and earns no native row credit. -/
def identity (b : Slice U8) := mapOuter NJQ_Carrier.identity_result (NJQ_Identity.model b)
theorem identity_result (b : Slice U8)  (out : core.result.Result NJQ_Carrier.I NJI_PolicyPort.F)
 (h : NJQ_IdentityCut.Cut b out) : ok (NJQ_Carrier.identity_result out)=identity b := by
 have same:=NJQ_IdentityCut.native_source b out h
 rw [NJQ_Identity.source] at same
 exact congrArg (mapOuter NJQ_Carrier.identity_result) same
set_option pp.proofs false in
#print identity_result
#print axioms identity_result

/-- Concrete natural model on the adopted carrier. This alone is not an
identification with an opaque cohort slot and earns no native row credit. -/
def master (b : Slice U8) := mapOuter NJQ_Carrier.master_result (NJQ_Master.model b)
theorem master_result (b : Slice U8)  (out : core.result.Result NJQ_Carrier.M NJQ_Carrier.F)
 (h : NJQ_MasterTotal.Cut b out) : ok (NJQ_Carrier.master_result out)=master b := by
 have same:=NJQ_MasterTotal.native_source b out h
 rw [NJQ_Master.source] at same
 exact congrArg (mapOuter NJQ_Carrier.master_result) same
set_option pp.proofs false in
#print master_result
#print axioms master_result

/-- Concrete natural model on the adopted carrier. This alone is not an
identification with an opaque cohort slot and earns no native row credit. -/
def checkpoint (b : Slice U8) := mapOuter NJQ_Carrier.checkpoint_result (NJQ_Checkpoint.model b)
theorem checkpoint_result (b : Slice U8)  (out : core.result.Result NJQ_Carrier.C NJQ_Carrier.F)
 (h : NJQ_CheckpointTotal.Cut b out) : ok (NJQ_Carrier.checkpoint_result out)=checkpoint b := by
 have same:=NJQ_CheckpointTotal.native_source b out h
 rw [NJQ_Checkpoint.source] at same
 exact congrArg (mapOuter NJQ_Carrier.checkpoint_result) same
set_option pp.proofs false in
#print checkpoint_result
#print axioms checkpoint_result
end NJQ_Canonical
