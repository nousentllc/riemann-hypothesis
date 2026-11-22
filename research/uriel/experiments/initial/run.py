"""Run experiments and tests; emit auditable JSON, report, and a test transcript."""
import argparse
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

import numpy
import scipy

from mechanisms import analytic,arithmetic,cohomology,covolume
from source_audit import audit,HERE,PIN,BASE


def dump(path,data):
    path.write_text(json.dumps(data,indent=2,sort_keys=True,allow_nan=False)+'\n')


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,default=HERE/'results')
    args=parser.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    start=time.monotonic();started_utc=datetime.now(timezone.utc).isoformat()
    numerical=dict(analytic=analytic(),arithmetic=arithmetic(),cohomology=cohomology(),covolume=covolume())
    source=audit()
    dump(args.out/'numerical.json',numerical);dump(args.out/'source_graph.json',source)
    test=subprocess.run([sys.executable,'-m','unittest','-v','test_suite'],cwd=HERE,text=True,capture_output=True)
    (args.out/'tests.txt').write_text(test.stdout+test.stderr)
    files={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in HERE.iterdir() if p.suffix in ['.py','.txt'] or p.name=='PREREGISTRATION.md'}
    provenance=dict(started_utc=started_utc,source_pin=PIN,research_parent=BASE,
                    preregistration_commit='9525c5b',python=sys.version,platform=platform.platform(),
                    numpy=numpy.__version__,scipy=scipy.__version__,elapsed_seconds=time.monotonic()-start,
                    test_exit_code=test.returncode,input_sha256=files,full_lean_build=False,kernel_replay=False)
    dump(args.out/'run.json',provenance)
    source_map=['# Pinned declaration and assumption map','',
                'Source-inspected declarations only. Body references are not kernel dependency edges.',
                'Imports unresolved in this selected corpus: '+str(sum(not e['resolved_in_selected_corpus'] for e in source['imports'])),
                '', '| Declaration | Original source | Visible body references |', '|---|---|---|']
    for n in source['nodes']:
        refs=[e['reference'] for e in source['edges'] if e['source']==n['id']]
        source_map.append('| `'+n['name']+'` | ['+Path(n['path']).name+':'+str(n['line'])+']('+n['url']+') | '+', '.join('`'+r+'`' for r in refs)+' |')
    source_map += ['', '## Guarded assumptions', '',
                   'Mutation tests check occurrence counts of exact source fragments. They are syntactic guards, not semantic theorem equivalence checks.', '']
    for g in source['guards']:
        url=f'https://github.com/nousentllc/riemann-hypothesis/blob/{PIN}/{g["path"]}#L{g["line"]}'
        source_map.append('- ['+g['declaration']+']('+url+'): `'+g['token']+'`.')
    (args.out/'SOURCE_MAP.md').write_text('\n'.join(source_map)+'\n')
    a=numerical['analytic'];b=numerical['arithmetic'];c=numerical['cohomology'];d=numerical['covolume']
    sel=[r for r in b['selected'] if r['admissible']]
    report=f'''# Executed initial mechanism suite

Source pin: `{PIN}`. Research parent: `{BASE}`.
Preregistration committed as `9525c5b` before suite execution.
Evidence: independent finite exploration and pinned-source inspection; no new kernel proof.

| Experiment | Measured result |
|---|---|
| Analytic residue control | At U=256, positive-residue log(mass/allowance) = {a['windows'][-1]['positive_log_ratio']:.9g}; negative-residue mass = 0 |
| High derivatives | 24 quadrature comparisons; max relative discrepancy {max(r['relative_error'] for r in a['quadrature']):.3g} |
| Source tail choice | {sum(r['passes'] for r in a['tails'])}/9 source-constant checks pass |
| Low-sigma ablation | sigma=3 scaled-tail log grows from {a['low_sigma'][0]['log_scaled_tail']:.6g} to {a['low_sigma'][-1]['log_scaled_tail']:.6g} |
| Coupled budget | {len(sel)}/9 selected-scale rows admissible; {sum(r['bound_passes'] for r in sel)}/{len(sel)} meet the conditional envelope; {sum(r['admissible'] and r['bound_passes'] for r in b['sampled'])}/900 seeded rows meet both |
| Budget identity | 200 independent normalizations; max relative discrepancy {b['identity_max_relative_error']:.3g} |
| Arithmetic ablations | {sum(not r['admissible'] for r in b['ablations'])}/5 rejected by constraints; {sum(not r['bound_passes'] for r in b['ablations'])}/5 exceed the envelope |
| Amplified weak-error control | exact x^10 / (x^5*(x+3)) = {b['weak_counterexample']['ratio']:.9g} at x=100000 |
| Finite-exception selector | {c['cases']} exact-rational whole-interval cases; {len(c['failures'])} failures |
| Slope lemma | 500 exact-rational witnesses; {len(d['numeric_failures'])} failures; 4 single-hypothesis counterexamples |
| Synthetic lattices | {len(d['lattices'])} projection/lattice cases; denominator-free cut fails in all |
| Source trace | {source['prior_trace_files']} prior hashes checked; {len(source['files'])} pinned source files; {len(source['edges'])} curated references; {len(source['failures'])} trace failures |
| Regression suite | exit {test.returncode}; see tests.txt |

Elapsed local runtime (including independent test rerun): {provenance['elapsed_seconds']:.3f} seconds.

## Interpretation limits

The source tail constants, real-pole sign, coupled rank/density bounds, and denominator
penalty matter in the tested models. Ablated failures are counterexamples to simplified
explanations, not counterexamples to the pinned theorem. The arithmetic grid instantiates
continuous scale inequalities, not actual arithmetic groups, theta lifts, or every source
hypothesis. Exact-rational interval checks test the selector, not cohomology or Sha lengths.
Euclidean lattices do not instantiate the full arithmetic number-field setting.

Full Lean build and kernel replay were **not attempted**: the original pin requires
v4.33.1, the research tree declares v4.36.0, the installed toolchain is recorded in
source_graph.json, and the selected sparse checkout has no dependency/build cache.
The module/import graph and body-reference graph are lexical and partial, not an
elaborated dependency closure or an axiom audit. External verification remains separately
reported at [MIT's verification record](https://math.mit.edu/~drew/grh/), last updated
2026-11-22 16:20 UTC when inspected; this run does not reproduce those checks.

See ../INTERPRETATION.md for the critique, deviations, uncertainty, and next experiments.
'''
    (args.out/'REPORT.md').write_text(report)
    print(report)
    return test.returncode


if __name__=='__main__':
    raise SystemExit(main())
