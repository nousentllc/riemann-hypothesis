"""Check the finite carry identities in the written all-height relative class number argument."""
import json


def unit_orbit(generator, modulus, order):
    value = 1
    out=[]
    for _ in range(order):
        out.append(value)
        value=value*generator % modulus
    assert value==1 and len(set(out))==order
    return out


def results():
    p,g=7,3
    omega=[z for z in range(1,p) if pow(z,3,p)==p-1]
    base_orbit=unit_orbit(g,p,6)
    base_digits=[g*u//p for u in base_orbit]
    records=[]
    for n in range(1,7):
        q=p**n
        lifts=q//p
        m=3*lifts
        orbit=unit_orbit(g,q,2*m)
        digits=[g*u//q for u in orbit]
        assert all(g*u-q*b==orbit[(j+1)%(2*m)] for j,(u,b) in enumerate(zip(orbit,digits)))
        assert orbit[m]==q-1 and all(orbit[i]+orbit[i+m]==q for i in range(m))
        projected=[sum(digits[r::6]) for r in range(6)]
        constant=(g-1)*(lifts-1)//2
        assert projected==[b+constant for b in base_digits]
        mod_poly=[projected[i]-projected[i+3] for i in range(3)]
        assert mod_poly==[-2,0,-2]
        odd_evals=[]
        for z in omega:
            value=0
            for b in reversed(digits):
                value=(value*z+b)%p
            assert value==sum(b*pow(z,k,p) for k,b in enumerate(base_digits))%p
            odd_evals.append(value)
        prod=1
        for v in odd_evals:
            prod=(prod*v)%p
        res=pow(prod,lifts,p)
        denominator_remainder=pow(g,m,p*q)+1
        assert denominator_remainder%q==0
        reduced=(denominator_remainder//q)%p
        assert reduced==4
        rel=2*(-1)**m*res*pow(pow(2,m,p)*reduced,-1,p)%p
        assert rel==1
        records.append(dict(exponent=n,conductor=q,pairs=m,common_constant=constant,
                            projection=mod_poly,modular_odd_values=odd_evals,resultant_mod7=res,
                            reduced_denominator_mod7=reduced,relative_class_number_mod7=rel,
                            unreduced_denominator_mod7=(pow(g,m,p)+1)%p))
    # Omitting the final carry in the cyclic sum spoils its projections at every odd root.
    missing_last=base_digits[:-1]+[0]
    damaged=[sum(v*pow(z,j,p) for j,v in enumerate(missing_last))%p for z in omega]
    assert damaged!=records[0]['modular_odd_values']
    return dict(generator=g,mod7_odd_roots=omega,base_orbit=base_orbit,base_carries=base_digits,
                wraparound_omitted_control=damaged,rows=records)


if __name__=="__main__":
    print(json.dumps(results(),indent=2))
