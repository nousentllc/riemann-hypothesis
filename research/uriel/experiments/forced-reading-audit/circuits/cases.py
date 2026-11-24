"""Render all joint observation cells, using stable opaque IDs and exact signed currents."""
import argparse
from fractions import Fraction
import hashlib
from itertools import product
import json
from pathlib import Path
from string import ascii_uppercase
from network import all_states, network_edges

HERE=Path(__file__).resolve().parent


def shuffled(sequence,salt):
    return sorted(sequence,key=lambda x:hashlib.sha256((salt+':'+x).encode()).digest())


def state_ids(keys):
    pool=[''.join(q) for q in product(ascii_uppercase,repeat=2)]
    original=set(shuffled(pool,'net-ref-2026')[:64])
    previous=set(shuffled([q for q in pool if q not in original],'threshold-bits-20261124')[:48])
    fresh=shuffled([q for q in pool if q not in original|previous],'forced-lamps-20261124')
    return {k:fresh[i*8:i*8+8] for i,k in enumerate(sorted(keys))}


def probe_description(probe):
    channel,cut=probe
    if channel.startswith('V'):
        return f'voltage at {channel[1:]} > {cut} V'
    return f'signed current of R{channel[1:]} > {cut} A'


def lamp(values,probe):
    return 'H' if values[probe[0]]>Fraction(probe[1]) else 'L'


def build():
    specs=json.loads((HERE/'design.json').read_text())
    labels=state_ids(specs)
    records={}
    for name,param in sorted(specs.items()):
        graph=network_edges(param['layout'])
        nets=[]
        for i,(u,v,r,sw) in enumerate(graph,1):
            nets.append(f'R{i}={u}>{v}:{r}'+('' if sw=='-' else '['+sw+']'))
        text=('DC network with + at 12 V and 0 at 0 V. Switch order is s,t,u (1 means closed). '
              'A bracketed resistor conducts only when its switch is closed. Each resistor lists its oriented start and end nodes and its resistance in ohms. '
              +' '.join(nets)+'.')
        ids=labels[name];table_order=shuffled(ids,'display:'+name)
        meters=shuffled(['M2','M3','M4','M5','M6','M7','M8'], 'forced-meter:'+name)[:2]
        decoy,decisive=meters
        menu_specs={decisive:param['decisive'],decoy:param['other']}
        # Presentation order is independent of which column is decisive.
        menu={k:probe_description(menu_specs[k]) for k in sorted(menu_specs)}
        states={}
        for ident,(bits,values) in zip(ids,all_states(graph)):
            states[ident]=dict(bits=bits,target_current=str(values[param['target'][0]]),answer=lamp(values,param['target'])=='H',
                initial=lamp(values,param['initial']),obs={k:lamp(values,menu_specs[k]) for k in menu})
        eligible=[s for s in table_order if states[s]['initial']==param['initial_reading']]
        observations=[('decisive',decisive,'L'),('decisive',decisive,'H'),('ambiguous',decoy,param['other_reading'])]
        # Rotate the three stored record types. Record IDs are administrative and hidden.
        offset=(int(name[1:])-1)%3
        observations=observations[offset:]+observations[:offset]
        for kind,meter,reading in observations:
            survivors=[s for s in eligible if states[s]['obs'][meter]==reading]
            record=dict(family='DC-'+name,states=states,target_threshold=param['target'][1],
                initial_reading=param['initial_reading'],meter=meter,reading=reading,kind=kind,
                eligible=eligible,survivors=survivors,description=text,signed_branch='R'+param['target'][0][1:],
                state_order=table_order,menu=menu,initial_description=probe_description(param['initial']))
            records[f'forced-{len(records):02d}']=record
    return records


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--write',action='store_true')
    fresh=build(); path=HERE/'records.json'
    if p.parse_args().write:path.write_text(json.dumps(fresh,indent=2)+'\n')
    elif json.loads(path.read_text())!=fresh:raise ValueError('Stored physical records differ')
    print(f'{len(fresh)} forced observations.')
