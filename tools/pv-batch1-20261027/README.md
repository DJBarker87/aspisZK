# Task-private gate scripts

`build.py`, `capped-template.py`, `rustc-diagnostics.py`, `devnet-ids.json` were copied from the base candidate’s rebase3 recipe, changing the task directory only. `gates.py` called only its sbf route and stopped at the initial metadata failure. A completed source snapshot was then rebuilt through build.py, which stopped on the default pin mismatch.

`native.py`, `compare-fixtures.py` and `extract.py` were prepared but NEVER executed. They are drafts for a possible lead-authorized resume and supply no evidence. No shared launcher, extractor, backend or env-J source was changed.

The failed default comparison is decisive under the task stop rule; these scripts must not be used to continue the gate sequence without lead review.
