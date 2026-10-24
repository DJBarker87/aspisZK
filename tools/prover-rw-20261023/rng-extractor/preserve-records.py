"""Retain the three pinned transparent record declarations, not tuple aliases.

The source/type identity check is exact; unrelated tuple-struct behavior stays
in the inherited backend. This is an experimental source change for build004.
"""
from pathlib import Path
D=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/rng-extractor')
p=D/'base/src/llbc/TypesAnalysis.ml'
s=p.read_text()
needle='    !Config.use_tuple_structs && (not is_rec) && type_decl_is_tuple_struct def'
assert s.count(needle)==1
s=s.replace(needle,'''    let retained_refined_record =
      match def.item_meta.name with
      | [PeIdent ("core",0); PeIdent ("num",0); PeIdent ("niche_types",0); PeIdent ("NonZeroI32Inner",0)]
      | [PeIdent ("core",0); PeIdent ("num",0); PeIdent ("nonzero",0); PeIdent ("NonZero",0)]
      | [PeIdent ("getrandom",0); PeIdent ("error",0); PeIdent ("Error",0)] -> true
      | _ -> false
    in
    !Config.use_tuple_structs && (not retained_refined_record)
    && (not is_rec) && type_decl_is_tuple_struct def''')
p.write_text(s)
p=D/'build-base.sh'
s=p.read_text().replace('export AENEAS_VERSION=b59d5188-lean432-extended',
    'export AENEAS_VERSION=b59d5188-lean432-extended-ProverRwRngExtractor')
p.write_text(s)
print('Retained exact three transparent outer records; candidate version label')
