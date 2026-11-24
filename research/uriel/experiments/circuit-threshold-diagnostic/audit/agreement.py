"""Characterize meter/target agreement on frozen records before consulting model decisions."""
from fractions import Fraction
import json
from check import ROOT, inspect_panel


def agreement(ids, meter, case):
    """Signed excess of matching Y/H or N/L pairs over mismatches."""
    aligned = sum((sid in case['positive']) == (case['meters'][sid][meter] == 'H') for sid in ids)
    return 2*aligned-len(ids)


def main():
    _,cases,_,_ = inspect_panel()
    rows = {}
    for rid,c in cases.items():
        if c['kind']!='lookup':
            continue
        match = {m:agreement(c['live'],m,c) for m in c['menu']}
        unfiltered = {m:agreement(c['meters'],m,c) for m in c['menu']}
        winner, = c['certain']
        if abs(match[winner])!=len(c['live']) or any(match[m]!=0 for m in c['menu'] if m!=winner):
            raise ValueError(f'Meter agreement disagrees with the partitions of {rid}.')
        best = max(abs(s) for s in unfiltered.values())
        tied = [m for m,s in unfiltered.items() if abs(s)==best]
        rows[rid] = dict(family=c['family'],correct_meter=winner,
                         H_licenses='Y' if match[winner]>0 else 'N',
                         agreement_on_admissible_rows=match,agreement_on_all_rows=unfiltered,
                         globally_maximal=tied,unfiltered_success_probability=str(Fraction(int(winner in tied),len(tied))))
    expectation = sum(Fraction(r['unfiltered_success_probability']) for r in rows.values())
    summary = dict(definition='Agreement uses +1 for Y/H and N/L, -1 for Y/L and N/H.',
                   scope='Frozen case construction; outcome-independent descriptive diagnostic.',
                   state_restriction='Four admissible rows conditioned on the observed initial lamp; eight before it.',
                   inverse_lamp_semantics=sum(r['H_licenses']=='N' for r in rows.values()),
                   expectation_under_uniform_unfiltered_ties=str(expectation),records=rows)
    output = json.dumps(summary,indent=2,ensure_ascii=False)+'\n'
    (ROOT/'audit/agreement.json').write_text(output)
    print(output.rstrip())


if __name__=='__main__':
    main()
