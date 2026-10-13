#!/usr/bin/env python3
from pathlib import Path
import json,re,sys
root=Path(__file__).resolve().parents[2]
pins=json.loads((root/'lean/comparator/pins.json').read_text())
text=Path(sys.argv[1]).read_text()
names=pins['targets']+['EntropicRogersShephard.complete_sharp_entropic_rogers_shephard']
records={}
for name in names:
    match=re.findall("'"+re.escape(name)+r"' depends on axioms: \[(.*?)\]",text,re.S)
    if len(match)!=1: raise SystemExit('Missing or duplicate axiom receipt: '+name)
    axioms=[x.strip() for x in match[0].split(',') if x.strip()]
    if set(axioms)-{'propext','Classical.choice','Quot.sound'}: raise SystemExit('Unexpected axiom: '+name)
    records[name]=axioms
if 'sorryAx' in text or 'error:' in text: raise SystemExit('Axiom audit failed')
Path(sys.argv[2]).write_text(json.dumps({'status':'PASS','targets':records,'sorryAx':False,'new_axioms':False},indent=2)+'\n')
print('PASS: all five comparator targets and the complete main theorem use permitted axioms.')
