#!/usr/bin/env python3
"""Offline synthetic demonstration; no actual payment or source proof claim."""
import json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from aspis_completion.security import diagnostic_report
from aspis_completion.wire import Wire,synthetic_body
from aspis_completion.finite_rom import enumerate_rom

body=bytearray(synthetic_body());a=Wire.parse(body);body[16]=1;b=Wire.parse(body)
rom=enumerate_rom(8,4,lambda h:None if any(s.answer==0 for s in h) else len(h),
                  lambda h,m:frozenset({0}))
print(json.dumps({'wire_mutation':{'same_roots':a.roots==b.roots,'same_fields':a.fields==b.fields,
               'same_body':a.body==b.body},
      'toy_adaptive_rom':{'alphabet':8,'max_calls':4,'bad_mass':str(rom.bad_mass)},
      'arithmetic':diagnostic_report()},indent=2))
