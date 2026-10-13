#!/usr/bin/env python3
"""Check the minimal FC draft against the canonical definitions and primary target."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2]
draft=(root/'FClikelean/EntropicRogersShephard.lean').read_text()
defs=(root/'lean/FCTargetDefinitions.lean').read_text()
challenge=(root/'lean/Challenge.lean').read_text()
imports=re.findall(r'^public import (\S+)',draft,re.M)
if imports!=['FormalConjecturesUtil']: raise SystemExit('Unexpected FC draft imports')
def clean(text):
    text=re.sub(r'/-[\s\S]*?-/', '', text)
    return re.sub(r'\s+',' ',text).strip()
mathematics=draft.split('@[expose] public section\n\n',1)[1]
mathematics=re.sub(r'@\[category research solved, AMS 52 60 94,\n    formal_proof using lean4 at "[^"\n]+"\]\n','',mathematics)
essential=defs[defs.index('def ProbabilityDensity '):defs.index('noncomputable def differenceDensity ')].rstrip()
target=re.search(r'^theorem entropic_rogers_shephard [\s\S]*? := by\n  sorry\n',challenge,re.M)
if target is None: raise SystemExit('Missing primary Comparator target')
expected='namespace EntropicRogersShephardFC\nopen MeasureTheory ProbabilityTheory\nopen scoped ENNReal\n'+essential+'\n'+target.group()+'\nend EntropicRogersShephardFC'
if clean(mathematics)!=clean(expected): raise SystemExit('FC draft mathematical body differs')
if len(re.findall(r'^def ',draft,re.M))!=2 or len(re.findall(r'^theorem ',draft,re.M))!=1:
    raise SystemExit('FC draft should contain two definitions and one theorem')
print('PASS: two definitions and the primary FC theorem match the canonical target.')
