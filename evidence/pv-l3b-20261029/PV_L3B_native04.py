from pathlib import Path
import sys,json,lzma,collections
D=Path(__file__).resolve().parent
sys.path.insert(0,str(D/'python'))
from elftools.elf.elffile import ELFFile
from elftools.dwarf.ranges import BaseAddressEntry,RangeEntry
def txt(v):return v.decode(errors='replace') if isinstance(v,bytes) else v
with (D/'client-target/release/devnet_spend').open('rb') as f:
 e=ELFFile(f);dw=e.get_dwarf_info();rows=[];counts=collections.Counter()
 for cu in dw.iter_CUs():
  top=cu.get_top_DIE();base=top.attributes.get('DW_AT_low_pc');base=base.value if base else 0
  lp=dw.line_program_for_CU(cu)
  def attr(d,k):
   if k in d.attributes:return d.attributes[k].value
   for ref in ['DW_AT_abstract_origin','DW_AT_specification']:
    if ref in d.attributes:return attr(d.get_DIE_from_attribute(ref),k)
   return None
  def file(i):
   if i is None or lp is None:return None
   files=lp['file_entry'];idx=i if cu['version']>=5 else i-1
   if idx<0 or idx>=len(files):return f'UNRESOLVED_FILE_INDEX:{i}'
   ent=files[idx];name=txt(ent.name);dirs=lp['include_directory'];di=ent.dir_index
   dn=txt(dirs[di]) if cu['version']>=5 and di<len(dirs) else (txt(dirs[di-1]) if di and di<=len(dirs) else txt(top.attributes.get('DW_AT_comp_dir').value) if 'DW_AT_comp_dir' in top.attributes else '')
   return str(Path(dn)/name)
  def ranges(d):
   a=d.attributes
   if 'DW_AT_low_pc' in a and 'DW_AT_high_pc' in a:
    lo=a['DW_AT_low_pc'].value;h=a['DW_AT_high_pc'];return [[lo,h.value if h.form=='DW_FORM_addr' else lo+h.value]]
   if 'DW_AT_ranges' in a:
    out=[];b=base
    for r in dw.range_lists().get_range_list_at_offset(a['DW_AT_ranges'].value,cu):
     if isinstance(r,BaseAddressEntry):b=r.base_address
     elif isinstance(r,RangeEntry):out.append([r.begin_offset+(0 if r.is_absolute else b),r.end_offset+(0 if r.is_absolute else b)])
    return out
   return []
  def walk(d,stack):
   counts[d.tag]+=1
   if d.tag in ['DW_TAG_subprogram','DW_TAG_inlined_subroutine']:
    rr=ranges(d)
    if rr:
     row=dict(die=hex(d.offset),tag=d.tag,name=txt(attr(d,'DW_AT_name')),linkage_name=txt(attr(d,'DW_AT_linkage_name')),ranges=rr,decl_file=file(attr(d,'DW_AT_decl_file')),decl_line=attr(d,'DW_AT_decl_line'),call_file=file(attr(d,'DW_AT_call_file')),call_line=attr(d,'DW_AT_call_line'),parents=stack)
     rows.append(row);stack=stack+[dict(name=row['name'],die=row['die'])]
   for child in d.iter_children():walk(child,stack)
  walk(top,[])
with lzma.open(D/'dwarf-all-instances.json.xz','wt') as f:json.dump(rows,f)
need=['no_pole','lean_copy_row_values','copy_tuple_limb','copy_endpoint_values','compress_tuple','equal','keep_clear','all_slots_clear','ct_','try_inv','inv','qm31_m31_dot','build_with_material']
selected=[r for r in rows if any(x in (r['name'] or '') for x in need) or any(x in (r['linkage_name'] or '') for x in ['ct_pole','wide_exact','CodeField'])]
(D/'dwarf-kernel-instances.json').write_text(json.dumps(selected,indent=2)+'\n')
(D/'dwarf-summary.json').write_text(json.dumps(dict(counts=counts,concrete_instances=len(rows),selected=len(selected),scope='exhaustive DIE traversal of diagnostic companion, subject to compiler DWARF completeness; attribution to deployed image depends on identity check'),indent=2)+'\n')
print(len(rows),len(selected))
