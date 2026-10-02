#!/usr/bin/env python3
from pathlib import Path
import hashlib
p=Path('/home/dombarker/project-offloads/aspis-r360-comment-context-candidate-20261002-a/src/extract/ExtractTypes.ml')
expected='cb59112741c428671764a44af7478117d2a324270ac0aec5c41052a3a2833a25'
old=p.read_text()
assert hashlib.sha256(old.encode()).hexdigest()==expected
before='''    | None, _ -> []
    | Some name, None ->
        [
          "Name pattern: ["
          ^ name_to_pattern_string (Some span) ctx.trans_ctx name
          ^ "]";
        ]
'''
insert='''    | None, _ -> []
    | Some name, _
      when List.exists (function Types.PeInstantiated _ -> true | _ -> false) name ->
        [
          "Instantiated source name: ["
          ^ name_to_string ctx name
          ^ "]";
        ]
    | Some name, None ->
        [
          "Name pattern: ["
          ^ name_to_pattern_string (Some span) ctx.trans_ctx name
          ^ "]";
        ]
'''
assert old.count(before)==1
new=old.replace(before,insert)
after='0f8ee29aa89c9456ea6c266ff8d767dcb8a83af5bbe8096d04e53582cb32c527'
assert hashlib.sha256(new.encode()).hexdigest()==after
p.write_text(new)
print({'path':str(p),'before_sha256':expected,'after_sha256':after,'changed_occurrences':1})
