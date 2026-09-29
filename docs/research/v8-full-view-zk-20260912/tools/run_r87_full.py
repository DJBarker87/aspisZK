#!/usr/bin/env python3
"""Reuse complete runner; only the preparation source checker changes."""
from pathlib import Path
source=Path(__file__).with_name('run_r85_full.py').read_text()
source=source.replace("and 'r85_native' in m", "and 'r85_native' in m and 'r87_prepare' in m")
source=source.replace("'profile_control':m['r85_native']['control']", "'profile_control':m['r87_prepare']['control']")
exec(compile(source,str(Path(__file__).with_name('run_r85_full.py')),'exec'))
