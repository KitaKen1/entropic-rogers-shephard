#!/usr/bin/env python3
"""Check fixed targets, pinned proof sources and identical auxiliary sources."""
from pathlib import Path
import argparse, hashlib, json, re, subprocess
ROOT=Path(__file__).resolve().parents[2]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,msg):
    if not ok: raise SystemExit(msg)
def statements(text):
    return re.findall(r"^theorem ([\s\S]*?) := by\n",text,re.M)
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--receipt-dir',type=Path);args=ap.parse_args()
    pins=json.loads((ROOT/'lean/comparator/pins.json').read_text())
    config=json.loads((ROOT/'lean/comparator.json').read_text())
    require(config['theorem_names']==pins['targets'] and len(pins['targets'])==5,'Incomplete target list')
    require(config['challenge_module']=='Challenge' and config['solution_module']=='FCSolution','Wrong modules')
    require(sorted(config['permitted_axioms'])==['Classical.choice','Quot.sound','propext'],'Wrong axiom permissions')
    for name,expected in pins['files_sha256'].items():
        require((ROOT/name).is_file() and sha(ROOT/name)==expected,'Pinned file changed: '+name)
    require((ROOT/'lean/lean-toolchain').read_text().strip()==pins['lean_toolchain'],'Wrong toolchain')
    require(pins['lean_toolchain']==pins['fc_upstream_toolchain']=='leanprover/lean4:v4.33.1',
      'Proof and FC must both use Lean 4.33.1')
    for name in ['comparator','lean4export']:
        patch=pins['toolchain_patches'][name]
        require(patch['build']==pins['lean_toolchain'] and patch['changed_files']==['lean-toolchain'],
          'Invalid checker toolchain patch: '+name)
    deps={p['name']:p['rev'] for p in json.loads((ROOT/'lean/lake-manifest.json').read_text())['packages']}
    require(deps['mathlib']==pins['mathlib_commit'],'Wrong Mathlib')
    require((ROOT/'lean/lake-manifest.json').read_bytes()==(ROOT/'leanWithoutComparator/lake-manifest.json').read_bytes(),'Auxiliary dependencies changed')
    require((ROOT/'lean/lean-toolchain').read_bytes()==(ROOT/'leanWithoutComparator/lean-toolchain').read_bytes(),'Auxiliary toolchain changed')
    original=json.loads((ROOT/'lean/comparator/proof-source-manifest.json').read_text())
    for name,expected in original['files_sha256'].items():
        require(sha(ROOT/'lean'/name)==expected,'Pinned proof source changed: '+name)
    shared=json.loads((ROOT/'lean/comparator/shared-proof-sources.json').read_text())
    wanted={x['path'] for x in shared['shared_files']}
    actual={p.relative_to(ROOT/'leanWithoutComparator').as_posix() for p in (ROOT/'leanWithoutComparator').rglob('*.lean') if '.lake' not in p.parts}
    canonical={p.relative_to(ROOT/'lean').as_posix() for p in (ROOT/'lean').rglob('*.lean') if '.lake' not in p.parts and 'comparator' not in p.relative_to(ROOT/'lean').parts and p.name not in ['Challenge.lean','FCAudit.lean']}
    require(wanted==actual==canonical,'Missing or extra common Lean source')
    for item in shared['shared_files']:
        for folder in ['lean','leanWithoutComparator']:
            require(sha(ROOT/folder/item['path'])==item['sha256'],'Shared source differs: '+folder+'/'+item['path'])
    for folder in ['lean','leanWithoutComparator']:
        for name in wanted:
            text=(ROOT/folder/name).read_text()
            require(not re.search(r'^\s*(?:public )?import Challenge\b',text,re.M),'Proof imports the sorried challenge')
    challenge=(ROOT/'lean/Challenge.lean').read_text();solution=(ROOT/'lean/FCSolution.lean').read_text()
    require(statements(challenge)==statements(solution) and len(statements(solution))==5,'Target theorem statements differ')
    subprocess.run(['python3',str(ROOT/'lean/comparator/check-fc-draft.py')],check=True)
    require(challenge.count('  sorry\n')==5,'Unexpected challenge holes')
    require(not re.search(r'\b(?:sorry|admit)\b',solution),'Hole in solution bridge')
    defs=(ROOT/'lean/FCTargetDefinitions.lean').read_text()
    require(all(x.startswith('Mathlib.') for x in re.findall(r'^import (\S+)',defs,re.M)),'Target imports submitted proof')
    require(not re.search(r'\b(?:sorry|admit)\b|^axiom ',defs,re.M),'Hole in target definitions')
    commit=subprocess.check_output(['git','-C',str(ROOT),'rev-parse','HEAD'],text=True).strip()
    result={'input_check':'passed','tested_commit':commit,'pins':pins,'config':config,
      'pinned_proof_sources':len(original['files_sha256']),
      'identical_common_sources':len(wanted),'common_sources':shared,'targets':pins['targets']}
    if args.receipt_dir:
        args.receipt_dir.mkdir(parents=True,exist_ok=True)
        (args.receipt_dir/'input-check.json').write_text(json.dumps(result,indent=2)+'\n')
        for name in ['Challenge.lean','FCTargetDefinitions.lean','FCSolution.lean']:
            shutil_copy=ROOT/'lean'/name
            (args.receipt_dir/name).write_bytes(shutil_copy.read_bytes())
    print(f"PASS: {len(pins['targets'])} targets, {len(wanted)} identical shared sources, pinned 4.33.1 proof sources.")
if __name__=='__main__': main()
