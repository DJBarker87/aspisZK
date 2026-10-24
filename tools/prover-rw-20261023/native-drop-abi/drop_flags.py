"""Fail closed before a new Drop validation; does not mutate old receipts."""
from pathlib import Path
import hashlib
import re

CONFIG_SHA256 = '81dd9fdb863e2c5e05407991f680a1a3c33eb01c289bf309a67a6f50fa66b35d'

def assess(command, config, main):
    config, main = Path(config), Path(main)
    digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    assert digest(config) == CONFIG_SHA256, 'unsupported Config source'
    # Only accept one known option, with no later option capable of resetting it.
    assert command.count('-eval-drops') == 1, 'Drop validation requires explicit -eval-drops'
    assert all(not x.startswith('-eval-drops=') for x in command)
    text = main.read_text()
    assert re.search(r'"-eval-drops",\s*Arg.Clear drop_as_no_op,', text), 'unsupported flag binding'
    # Require the sole CLI binding of the flag: fail closed if source evolves.
    assert text.count('drop_as_no_op') == 3, 'unsupported flag source use count'
    return dict(command=command, all_flags=command[1:], config_sha256=digest(config),
                main_sha256=digest(main), effective_drop_as_no_op=False,
                accepted_artifact=False, assessment='explicit flag under pinned Config; not a semantic acceptance')
