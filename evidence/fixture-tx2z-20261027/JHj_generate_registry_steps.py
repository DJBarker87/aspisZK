from pathlib import Path
R=Path(__file__).resolve().parents[2]
header='''set_option autoImplicit false
noncomputable section
namespace AspisR1.{name}
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHg_World
attribute [local irreducible] e2 JHb_DataRegistry.value JHb_DataEntry.value
'''
args='''(JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool
      (e2.snapshot 1 384 384) JHg_AccountValues.master
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) slot'''
for name,slot,bytes,record,extra0,extra1,read,tail in [
 ('RegistryReadStep','op33','JHb_DataRegistry.value','registry',' JHb_Programs.registry JHj_RegistryValue.loader',' JHb_Programs.registry JHj_RegistryValue.loader JHj_RegistryValue.registry','RegistryRead','RegistryDecoded'),
 ('EntryReadStep','op34','JHb_DataEntry.value','entry',' JHb_Programs.registry JHj_RegistryValue.loader JHj_Seeds.key JHj_RegistryValue.loader',' JHb_Programs.registry JHj_RegistryValue.loader JHj_Seeds.key JHj_RegistryValue.loader JHj_RegistryValue.entry','EntryRead','EntryDecoded')]:
 name='JHj_'+name
 s=''.join('import '+i+'\n' for i in ['JHj_'+read,'JHj_'+tail,'JHj_RegistryReads','JHj_RegistryValue','JHd_ReferenceSlots'])
 s+=header.format(name=name)
 s+='\n/-- Exact real account read followed by the explicit native decoder observation. -/\ntheorem source (base : Ops) (slot : U64)\n    (decoded : (JHd_ReferenceSlots.install base).'+slot+' '+bytes+'=ok (.Ok JHj_RegistryValue.'+record+')) :\n    JHj_'+read+'.run '+args+extra0+'=\n    JHj_'+tail+'.run '+args+extra1+' := by\n  unfold JHj_'+read+'.run\n  rw [JHj_RegistryReads.'+record+',bind_tc_ok]\n  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]\n  rw [decoded,bind_tc_ok]\n  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]\n  rfl\n#print axioms source\nend AspisR1.'+name+'\nend\n'
 (R/'lean'/(name+'.lean')).write_text(s)
