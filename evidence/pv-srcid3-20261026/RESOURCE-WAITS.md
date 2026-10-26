# Resource refusals and retry correction

All refusals are retained in reservation-*.json/log, charged zero. Refused
Lean IDs are not reused. The scanner and shared launcher are unchanged.

At 18:46:39 UTC, 25339 was refused for aggregate reservation. A batched call
then attempted independent target 25340 at 18:46:39.985 instead of waiting
three minutes. That second reservation also refused, so neither launched a
capped scope or charged an attempt. This was a retry-cadence violation even
though the target differed. Subsequent launches are made one at a time with
the resource result inspected first. Next permitted retry: after 18:49:40 UTC.
