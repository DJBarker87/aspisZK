"""Toolchain policy based on the upstream opaque-value closure fix.
A version check is a minimum screen, not a review of all kernel vulnerabilities.
"""
import re
MIN_VALIDATION=(4,32,2)
def parse_version(text):
    m=re.search(r'version\s+(\d+)\.(\d+)\.(\d+)',text)
    if not m:raise ValueError('unrecognised Lean version output')
    return tuple(map(int,m.groups()))
def validation_permitted(text):
    return parse_version(text)>=MIN_VALIDATION
