#!/usr/bin/env python3
from pathlib import Path
import json,re,sys
root=Path(__file__).resolve().parents[2]
receipt=Path(sys.argv[1])
original=re.findall(r'^#print axioms (\S+)',(root/'lean/EntropicRogersShephard/Audit.lean').read_text(),re.M)
pins=json.loads((root/'lean/comparator/pins.json').read_text())
names=set(original+pins['targets'])
if len(original)!=446 or len(names)!=451: raise SystemExit('Incomplete full axiom audit coverage')
logs=(receipt/'axioms.log').read_text()+(receipt/'original-axioms.log').read_text()
records={}
for name in sorted(names):
    match=re.findall("'"+re.escape(name)+r"' depends on axioms: \[(.*?)\]",logs,re.S)
    empty=f"'{name}' does not depend on any axioms" in logs
    if not match and not empty: raise SystemExit('Missing axiom report: '+name)
    axioms=[x.strip() for x in (match[0] if match else '').split(',') if x.strip()]
    if set(axioms)-{'propext','Classical.choice','Quot.sound'}: raise SystemExit('Unexpected axioms: '+name)
    records[name]=axioms
if 'sorryAx' in logs or 'error:' in logs: raise SystemExit('Full axiom audit failed')
(receipt/'axioms-full.json').write_text(json.dumps({'status':'PASS','audited_targets':451,'original_targets':446,'new_fc_targets':5,'sorryAx':False,'new_axioms':False,'targets':records},indent=2)+'\n')
print('PASS: all 451 targets use only the three permitted logical axioms.')
