#!/usr/bin/env python3
"""Reconstruct and verify R344's single-file candidate from the frozen R312 source file."""
import hashlib
from pathlib import Path
root=Path(__file__).resolve().parent
src=root/'source-parent/interp/InterpExpansion.ml'
out=root/'candidate-source/interp/InterpExpansion.ml'
old='''  let variants_fields_types =
    Substitute.type_decl_get_instantiated_variants_fields_types span def
      generics
  in
  (* Check if there is strictly more than one variant *)
'''
new='''  let variants_fields_types =
    Substitute.type_decl_get_instantiated_variants_fields_types span def
      generics
  in
  (* A direct field of an enum with no constructors cannot have a typed value.
     Remove only variants whose instantiated fields directly name such an enum. *)
  let is_direct_empty_enum_field (ty : rty) =
    match ty with
    | TAdt { id = TAdtId field_def_id; _ } ->
        let field_def = ctx_lookup_type_decl span ctx field_def_id in
        begin
          match field_def.kind with
          | Enum [] -> true
          | _ -> false
        end
    | _ -> false
  in
  let variants_fields_types =
    List.filter
      (fun (_variant_id, field_types) ->
        not (List.exists is_direct_empty_enum_field field_types))
      variants_fields_types
  in
  (* Check if there is strictly more than one variant *)
'''
assert hashlib.sha256(src.read_bytes()).hexdigest()=='30dc6e75bdafa31d04b29784e8235306f569161dcd5c73f8381ae18cd17ff7cd'
s=src.read_text()
assert s.count(old)==1
expected=s.replace(old,new)
assert out.read_text()==expected
print({'parent_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'candidate_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'exact_patch_reconstruction':True,'substitution_count':1,'build_or_translation_run':False})
