import NDO_NCX_ZeroLaws
import JHg_AuditEntry
set_option autoImplicit false
namespace NCX_EntryFields
open Aeneas Aeneas.Std Result AspisR1
attribute [local irreducible] JHb_DataEntry.bytes

theorem read_version : Slice.index_usize JHb_DataEntry.value 4#usize=ok 3#u8 := by
  apply NCV_FieldViews.byte
  · have h:=JHb_DataEntry.length; change 4 < JHb_DataEntry.bytes.length;omega
  · exact JHg_AuditEntry.version
#print axioms read_version

theorem read_status : Slice.index_usize JHb_DataEntry.value 5#usize=ok 1#u8 := by
  apply NCV_FieldViews.byte
  · have h:=JHb_DataEntry.length; change 5 < JHb_DataEntry.bytes.length;omega
  · exact JHg_AuditEntry.status
#print axioms read_status

theorem read_statement_version : Slice.index_usize JHb_DataEntry.value 6#usize=ok 1#u8 := by
  apply NCV_FieldViews.byte
  · have h:=JHb_DataEntry.length; change 6 < JHb_DataEntry.bytes.length;omega
  · exact JHg_AuditEntry.statement_version
#print axioms read_statement_version

theorem read_mode : Slice.index_usize JHb_DataEntry.value 7#usize=ok 1#u8 := by
  apply NCV_FieldViews.byte
  · have h:=JHb_DataEntry.length; change 7 < JHb_DataEntry.bytes.length;omega
  · exact JHg_AuditEntry.mode
#print axioms read_mode

def pool : Array U8 32#usize := Array.make 32#usize ([34#u8,8#u8,198#u8,55#u8,61#u8,211#u8,19#u8,178#u8,242#u8,118#u8,165#u8,45#u8,20#u8,254#u8,147#u8,25#u8,55#u8,157#u8,211#u8,124#u8,152#u8,170#u8,59#u8,88#u8,182#u8,77#u8,252#u8,152#u8,45#u8,26#u8,82#u8,63#u8])
theorem read_pool : NCX_Reference.read32 JHb_DataEntry.value 8#usize=ok pool := by
  apply NCX_FieldLaws.read32
  · have h:=JHb_DataEntry.length; change 8+32 ≤ JHb_DataEntry.bytes.length;omega
  · exact JHg_AuditEntry.pool
#print axioms read_pool

def verifier : Array U8 32#usize := Array.make 32#usize ([95#u8,12#u8,126#u8,84#u8,84#u8,184#u8,191#u8,44#u8,127#u8,237#u8,85#u8,250#u8,26#u8,65#u8,11#u8,162#u8,234#u8,180#u8,193#u8,149#u8,162#u8,190#u8,100#u8,247#u8,226#u8,253#u8,59#u8,0#u8,225#u8,151#u8,154#u8,141#u8])
theorem read_verifier : NCX_Reference.read32 JHb_DataEntry.value 40#usize=ok verifier := by
  apply NCX_FieldLaws.read32
  · have h:=JHb_DataEntry.length; change 40+32 ≤ JHb_DataEntry.bytes.length;omega
  · exact JHg_AuditEntry.verifier
#print axioms read_verifier

def profile : Array U8 32#usize := Array.make 32#usize ([87#u8,148#u8,115#u8,19#u8,210#u8,50#u8,100#u8,26#u8,216#u8,21#u8,125#u8,102#u8,191#u8,175#u8,250#u8,177#u8,30#u8,76#u8,58#u8,153#u8,51#u8,29#u8,24#u8,244#u8,75#u8,250#u8,202#u8,182#u8,137#u8,151#u8,55#u8,211#u8])
theorem read_profile : NCX_Reference.read32 JHb_DataEntry.value 72#usize=ok profile := by
  apply NCX_FieldLaws.read32
  · have h:=JHb_DataEntry.length; change 72+32 ≤ JHb_DataEntry.bytes.length;omega
  · exact JHg_AuditEntry.profile
#print axioms read_profile

def release : Array U8 32#usize := Array.make 32#usize ([226#u8,148#u8,175#u8,188#u8,20#u8,239#u8,106#u8,254#u8,118#u8,184#u8,71#u8,222#u8,244#u8,68#u8,82#u8,248#u8,76#u8,195#u8,114#u8,128#u8,100#u8,101#u8,118#u8,7#u8,181#u8,68#u8,165#u8,57#u8,202#u8,155#u8,50#u8,58#u8])
theorem read_release : NCX_Reference.read32 JHb_DataEntry.value 104#usize=ok release := by
  apply NCX_FieldLaws.read32
  · have h:=JHb_DataEntry.length; change 104+32 ≤ JHb_DataEntry.bytes.length;omega
  · exact JHg_AuditEntry.release
#print axioms read_release

def loader : Array U8 32#usize := Array.make 32#usize ([2#u8,168#u8,246#u8,145#u8,78#u8,136#u8,161#u8,176#u8,226#u8,16#u8,21#u8,62#u8,247#u8,99#u8,174#u8,43#u8,0#u8,194#u8,185#u8,61#u8,22#u8,193#u8,36#u8,210#u8,192#u8,83#u8,122#u8,16#u8,4#u8,128#u8,0#u8,0#u8])
theorem read_loader : NCX_Reference.read32 JHb_DataEntry.value 136#usize=ok loader := by
  apply NCX_FieldLaws.read32
  · have h:=JHb_DataEntry.length; change 136+32 ≤ JHb_DataEntry.bytes.length;omega
  · exact JHg_AuditEntry.loader
#print axioms read_loader

def programdata : Array U8 32#usize := Array.make 32#usize ([9#u8,32#u8,132#u8,147#u8,91#u8,179#u8,5#u8,145#u8,236#u8,128#u8,247#u8,235#u8,169#u8,248#u8,96#u8,190#u8,113#u8,27#u8,13#u8,169#u8,128#u8,213#u8,131#u8,59#u8,122#u8,113#u8,158#u8,205#u8,89#u8,140#u8,195#u8,110#u8])
theorem read_programdata : NCX_Reference.read32 JHb_DataEntry.value 168#usize=ok programdata := by
  apply NCX_FieldLaws.read32
  · have h:=JHb_DataEntry.length; change 168+32 ≤ JHb_DataEntry.bytes.length;omega
  · exact JHg_AuditEntry.programdata
#print axioms read_programdata

def executable_hash : Array U8 32#usize := Array.make 32#usize (List.replicate 32 90#u8)
theorem read_executable_hash : NCX_Reference.read32 JHb_DataEntry.value 200#usize=ok executable_hash := by
  apply NCX_FieldLaws.read32
  · have h:=JHb_DataEntry.length; change 200+32 ≤ JHb_DataEntry.bytes.length;omega
  · exact JHg_AuditEntry.executable_hash
#print axioms read_executable_hash

def upgrade_authority : Array U8 32#usize := Array.make 32#usize (List.replicate 32 0#u8)
theorem read_upgrade_authority : NCX_Reference.read32 JHb_DataEntry.value 232#usize=ok upgrade_authority := by
  apply NCX_FieldLaws.read32
  · have h:=JHb_DataEntry.length; change 232+32 ≤ JHb_DataEntry.bytes.length;omega
  · exact JHg_AuditEntry.upgrade_authority
#print axioms read_upgrade_authority

def activation_bytes : Array U8 8#usize := Array.make 8#usize (List.replicate 8 0#u8)
def activation : U64 := core.num.U64.from_le_bytes activation_bytes
theorem read_activation : NCX_Reference.word JHb_DataEntry.value 264#usize=ok activation := by
  apply NCX_FieldLaws.word
  · have h:=JHb_DataEntry.length; change 264+8 ≤ JHb_DataEntry.bytes.length;omega
  · exact JHg_AuditEntry.activation
#print axioms read_activation

def retirement_bytes : Array U8 8#usize := Array.make 8#usize (List.replicate 8 255#u8)
def retirement : U64 := core.num.U64.from_le_bytes retirement_bytes
theorem read_retirement : NCX_Reference.word JHb_DataEntry.value 272#usize=ok retirement := by
  apply NCX_FieldLaws.word
  · have h:=JHb_DataEntry.length; change 272+8 ≤ JHb_DataEntry.bytes.length;omega
  · exact JHg_AuditEntry.retirement
#print axioms read_retirement

def policy : Array U8 32#usize := Array.make 32#usize (List.replicate 32 7#u8)
theorem read_policy : NCX_Reference.read32 JHb_DataEntry.value 280#usize=ok policy := by
  apply NCX_FieldLaws.read32
  · have h:=JHb_DataEntry.length; change 280+32 ≤ JHb_DataEntry.bytes.length;omega
  · exact JHg_AuditEntry.policy
#print axioms read_policy

theorem read_bump : Slice.index_usize JHb_DataEntry.value 312#usize=ok 254#u8 := by
  apply NCV_FieldViews.byte
  · have h:=JHb_DataEntry.length; change 312 < JHb_DataEntry.bytes.length;omega
  · exact JHg_AuditEntry.bump
#print axioms read_bump

theorem read_programdata_bump : Slice.index_usize JHb_DataEntry.value 313#usize=ok 254#u8 := by
  apply NCV_FieldViews.byte
  · have h:=JHb_DataEntry.length; change 313 < JHb_DataEntry.bytes.length;omega
  · exact JHg_AuditEntry.programdata_bump
#print axioms read_programdata_bump
end NCX_EntryFields
