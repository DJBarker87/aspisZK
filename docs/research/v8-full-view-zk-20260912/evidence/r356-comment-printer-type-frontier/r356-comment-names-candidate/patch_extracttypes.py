#!/usr/bin/env python3
from pathlib import Path
import hashlib
p=Path('/home/dombarker/project-offloads/aspis-r356-comment-names-candidate-20261002-a/src/extract/ExtractTypes.ml')
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
          ^ name_to_string ctx.trans_ctx name
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
after='2893509bb9fbbc159e9262532adab1d2b4f684b269f4e835d8cf5b6709188ddf'
assert hashlib.sha256(new.encode()).hexdigest()==after
p.write_text(new)
print({'path':str(p),'before_sha256':expected,'after_sha256':after,'changed_occurrences':old.count(before)})
