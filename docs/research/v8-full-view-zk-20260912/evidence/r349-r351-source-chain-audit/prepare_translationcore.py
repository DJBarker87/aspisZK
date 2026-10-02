#!/usr/bin/env python3
"""Deterministically verify the lead-specified one-file TranslateCore candidate."""
from pathlib import Path
import hashlib
root=Path(__file__).resolve().parent
src=root/'parent-source/src/TranslateCore.ml'
out=root/'candidate-source/src/TranslateCore.ml'
old='''let name_to_simple_name (ctx : trans_ctx) (n : Types.name) : string list =
  let mctx = Charon.NameMatcher.ctx_from_crate ctx.crate in
  name_to_simple_name mctx n

let name_with_generics_to_simple_name (ctx : trans_ctx)
    ?(prefix : Types.name option = None) (name : Types.name)
    (p : Types.generic_params) (g : Types.generic_args) : string list =
  let mctx = Charon.NameMatcher.ctx_from_crate ctx.crate in
  name_with_generics_to_simple_name mctx ~prefix name p g
'''
new='''let append_instantiated_name_suffix (ctx : trans_ctx) (source_name : Types.name)
    (extracted_components : string list) : string list =
  if List.exists (function Types.PeInstantiated _ -> true | _ -> false) source_name
  then
    let suffix =
      "_mono_" ^ Digest.to_hex (Digest.string (name_to_string ctx source_name))
    in
    match List.rev extracted_components with
    | last :: rest -> List.rev ((last ^ suffix) :: rest)
    | [] -> []
  else extracted_components

let name_to_simple_name (ctx : trans_ctx) (n : Types.name) : string list =
  let mctx = Charon.NameMatcher.ctx_from_crate ctx.crate in
  append_instantiated_name_suffix ctx n (ExtractName.name_to_simple_name mctx n)

let name_with_generics_to_simple_name (ctx : trans_ctx)
    ?(prefix : Types.name option = None) (name : Types.name)
    (p : Types.generic_params) (g : Types.generic_args) : string list =
  let mctx = Charon.NameMatcher.ctx_from_crate ctx.crate in
  append_instantiated_name_suffix ctx name
    (ExtractName.name_with_generics_to_simple_name mctx ~prefix name p g)
'''
assert hashlib.sha256(src.read_bytes()).hexdigest()=='2368456969bd85545b57cda2e701949b8814fc445a419b1e4e96795b91af57b7'
text=src.read_text()
assert text.count(old)==1
assert out.read_text()==text.replace(old,new)
print({'parent_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'candidate_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'exact_reconstruction':True,'changed_wrapper_block_count':1,'build_or_translation_run':False})
