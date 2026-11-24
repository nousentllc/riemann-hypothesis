"""Paired process diagnostics, conditional on each predeclared information stratum."""
import argparse
from collections import Counter
import json
from domain import ARMS, HERE, oracle, score_session, save

def summarize(model):
    registry='test-'+model
    directory=HERE/'observed'/registry
    rows=json.loads((HERE/'registry'/registry/'records.json').read_text())
    data={}; pairs=[]; error_examples=[]; diagnostics={a:{} for a in ARMS}
    for rid,row in rows.items():
        target=oracle(row)
        per={}
        for arm in ARMS:
            packet=json.loads((directory/(rid+'_'+arm)/'session.json').read_text())
            scored=score_session(row,packet); per[arm]=scored
            stats=diagnostics[arm].setdefault(row['domain']+'-'+target['kind'],Counter())
            stats['n']+=1
            stats['initial_warranted']+=scored['initial']['licensed']
            stats['initial_certified']+=scored['initial']['certified']
            stats['requested_measurement']+=scored['used'] in row['menu']
            stats['guaranteed_resolution_selected']+=scored['used'] in target['guaranteed'] if target['kind']=='lookup' else 0
            stats['wrong_or_unavailable_measurement']+=target['kind']=='lookup' and not scored['productive']
            enough=scored['final']['expected']==target['target']
            stats['same_lookup_perfect_reasoner_ceiling']+=enough
            if scored['pass_case']:
                bottleneck='pass'
            elif not enough:
                bottleneck='evidence_selection'
            elif scored['final']['verdict']!=target['target']:
                bottleneck='decision_or_missing'
            else:
                bottleneck='certificate'
            stats['first_failure_'+bottleneck]+=1
            stats['attained_verdict']+=scored['final']['verdict']==target['target']
            stats['attained_verdict_valid_certificate']+=scored['pass_case']
            stats['unnecessary_query_on_settled']+=target['kind']=='settled' and scored['used'] in row['menu']
            stats['final_abstained_despite_decisive_evidence']+=scored['final']['verdict']=='U' and scored['final']['expected']!='U'
            stats['unlicensed_initial_then_certified']+=scored['initial']['unsupported'] and scored['pass_case']
            if not scored['pass_case']:
                error_examples.append(dict(record=rid,family=row['family'],variant=row['variant'],arm=arm,
                    type=target['kind'],initial_warrant=target['initial'],initial=scored['initial']['verdict'],
                    lookup=scored['used'],decisive_available=target['guaranteed'],
                    final=scored['final']['verdict'],final_warrant=scored['final']['expected'],attainable=target['target'],
                    certificate_valid_for_received_evidence=scored['final']['certified']))
        pairs.append(dict(record=rid,domain=row['domain'],family=row['family'],variant=row['variant'],
                     outcome={a:per[a]['pass_case'] for a in ARMS},lookup={a:per[a]['used'] for a in ARMS}))
    counts=Counter((p['outcome']['general'],p['outcome']['method']) for p in pairs)
    data['diagnostics']=diagnostics
    data['paired_cases']=[{'general':g,'method':m,'n':counts[g,m]} for g in (False,True) for m in (False,True)]
    data['pairs']=pairs;data['errors']=error_examples
    save(HERE/'reports'/registry/'lookup_diagnostics.json',data)
    print(data['paired_cases'])
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('model',choices=['qwen','gptoss'])
    summarize(parser.parse_args().model)
