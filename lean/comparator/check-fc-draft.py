#!/usr/bin/env python3
"""Strip FC metadata and check the exact standalone mathematical definitions and targets."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2]
draft=(root/'FClikelean/EntropicRogersShephard.lean').read_text()
defs=(root/'lean/FCTargetDefinitions.lean').read_text()
challenge=(root/'lean/Challenge.lean').read_text()
imports=[x.removeprefix('public ') for x in draft.splitlines() if x.startswith('public import Mathlib.')]
if imports!=[x for x in defs.splitlines() if x.startswith('import ')]:
 raise SystemExit('FC draft Mathlib imports differ')
mathematics=draft.split('@[expose] public section\n\n',1)[1]
mathematics=re.sub(r'@\[category research solved, AMS 52 60 94,\n    formal_proof using lean4 at "[^"\n]+"\]\n','',mathematics)
expected=defs[defs.index('/-!'):]+challenge[len('import FCTargetDefinitions\n'):]
if mathematics!=expected: raise SystemExit('FC draft mathematical body differs')
print('PASS: FC draft definitions and all five statements match the standalone Challenge.')
