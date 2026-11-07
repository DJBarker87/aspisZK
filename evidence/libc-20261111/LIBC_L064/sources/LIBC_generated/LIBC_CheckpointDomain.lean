import LIBC_VStateCarriers
import LIBC_Bytes
import NGC_KNE_Final
set_option autoImplicit false
noncomputable section
namespace LIBC_CheckpointDomain
open Aeneas Aeneas.Std Result AspisR1 RSL
abbrev Args := LIB_VCarriers.Prepared × LIB_VCarriers.Acc × Bytes × Bytes
def prepared (a : Args) := CheckpointBytes3Namespaces.toPrepared (NFW_PreparedPort.prepared a.1)
def accumulator (a : Args) := CheckpointBytes3Namespaces.toAccumulator (LIBC_VStateCarriers.toAcc a.2.1)
def reached (a : Args) : CheckpointBytes5Writer.Prepared → CheckpointBytes5Writer.Accumulator → Prop :=
 fun p b => p=prepared a ∧ b=accumulator a
/-- Original DriverEstablishedDomain specialized to this one SAME input
pair, not a global-world or prior-result hypothesis on the leaf. -/
def Domain (a : Args) : Prop :=
 NGC_KNE_Caller.DriverEstablishedDomain (reached a) ∧
 a.2.2.1.length=57607 ∧ a.2.2.2.length=1880
theorem writer_domain (a : Args) (h : Domain a) :
 NGC_KNE_Caller.WriterDomain (prepared a) (accumulator a) :=
 NGC_KNE_Caller.every_reached_call (reached a) h.1 _ _ ⟨rfl,rfl⟩
/-- F6: no earlier parse/scan/prepare/heap/query successes enter the leaf.
NHS_CheckpointPacket derives this WriterDomain from those callers; the exact
current-pair driver clause is equivalent to these source-format input facts. -/
theorem driver_iff (a : Args) :
 NGC_KNE_Caller.DriverEstablishedDomain (reached a) ↔
 NGC_KNE_Caller.WriterDomain (prepared a) (accumulator a) := by
 constructor
 · intro h
   exact NGC_KNE_Caller.every_reached_call (reached a) h _ _ ⟨rfl,rfl⟩
 · intro d p b pair
   rcases pair with ⟨rfl,rfl⟩
   exact ⟨_,_,⟨d.variant,d.size,d.queriesBound,d.canonical,d.next,rfl,rfl⟩⟩
theorem from_writer (a : Args)
 (d : NGC_KNE_Caller.WriterDomain (prepared a) (accumulator a))
 (stored : a.2.2.1.length=57607) (public_ : a.2.2.2.length=1880) : Domain a :=
 ⟨(driver_iff a).mpr d,stored,public_⟩
#print axioms writer_domain
#print axioms driver_iff
#print axioms from_writer
end LIBC_CheckpointDomain
