"""Finite audit of marked supports, local endpoint transport, and dyadic rescaling."""
import itertools
import json
from fractions import Fraction as Q


def support_controls(m=4):
    """The final support may be a subset of the qualified support. Late membership is explicit."""
    all_masks = range(1 << m)
    universe = (1 << m) - 1
    fields = dict(scenarios=0, admissible=0, bare_failures=0, equal_support=0,
                  equal_support_failures=0, proper_marked_support=0, proper_marked_failures=0)
    example = None
    for raw, family, bad, cut in itertools.product(all_masks, all_masks, all_masks, range(m+1)):
        fields["scenarios"] += 1
        late = universe & ~((1 << cut)-1)
        if (family & ~raw) or (family & bad & late):
            continue
        fields["admissible"] += 1
        violation = raw & bad & late
        if violation:
            fields["bare_failures"] += 1
            if example is None and raw.bit_count() >= 2 and family.bit_count() >= 1 and cut == 0:
                example={"raw":raw,"family":family,"bad":bad,"violating_bits":violation}
        if raw == family:
            fields["equal_support"] += 1
            fields["equal_support_failures"] += bool(violation)
        for marked in all_masks:
            if marked != family and not (marked & ~family):
                fields["proper_marked_support"] += 1
                fields["proper_marked_failures"] += bool(marked & bad & late)
    assert fields["equal_support_failures"]==fields["proper_marked_failures"]==0
    assert fields["bare_failures"]>0 and example
    return dict(fields, example=example, bit_legend="The four bits are four ordered scales. Cut c discards the c smallest scales.")


def scale_controls():
    """Use logs to base two. The integer r is log2(k) and w is log2(W)."""
    checked=extended=fail_two=equal=0
    certificate=None
    for r in range(5):
        for w in [max(1,400*r),max(1,400*r)+1,max(1,400*r)+20]:
            for excess in range(2*r+3):
                U=2*w+excess
                lo=r+w
                hi=min(U,r+2*w)
                assert hi>=2*w
                for v in [lo-1,lo,(lo+hi)//2,hi,hi+1]:
                    interval=lo<=v<=hi
                    all_conditions=(w<=v-r<=2*w and v<=U)
                    assert all_conditions==interval
                    checked+=1
                for lam in [Q(3,2),Q(19,10),Q(199,100),Q(999,500),Q(2)]:
                    right=lam*lo
                    if lam<2:
                        room=(w>=lam*r/(2-lam))
                        assert room==(right<=2*w)
                    if lam==2 and right>hi:
                        fail_two+=1
                    if Q(3,2)*lo<right<=hi:
                        extended+=1
                equal+=hi==2*w
                if r==1 and w==400 and excess==0:
                    certificate={"log2_k":r,"log2_W":w,"log2_X":U,"log2_old_upper":str(Q(3,2)*lo),"log2_certified_upper":hi,"log2_double_width_upper":2*lo}
    return {"boundary_probes":checked, "larger_widths_admitted":extended,"width_two_fails_on_rescaled_block":fail_two,"right_edge_exactly_W_squared":equal,"hand_certificate":certificate}


def threshold_control():
    """A family chosen anew can certify eventuality and still yield no bound at its marked pair."""
    examples=[]
    for n in range(2,10):
        a,b=2*n,2*n+1
        cut=b+1
        good=lambda t:t not in (a,b)
        assert all(good(t) for t in range(cut,cut+20))
        assert not good(a) and not good(b)
        examples.append([a,b,cut])
    return examples


if __name__=="__main__":
    print(json.dumps({"truth_table":support_controls(),"dyadic":scale_controls(),"moving_cut_examples":threshold_control()},indent=2))
