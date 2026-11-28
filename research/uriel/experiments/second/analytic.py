"""Signed pole resolution and the scaled one-sided Landau estimate on closed windows."""
from fractions import Fraction as F
from mpmath import mp


def real(q):
    q = F(q)
    return mp.mpf(q.numerator) / q.denominator


def pole_probe(heights, residues, gamma):
    # Exact squared distances make midpoint classification independent of precision.
    gap = F(9, 4)
    dsq = [gap**2 + (gamma-w)**2 for w in heights]
    closest = [i for i, a in enumerate(dsq) if a == min(dsq)]
    row = dict(gamma=str(gamma), nearest=closest, distances_squared=list(map(str, dsq)))
    if len(closest) != 1:
        return row
    i, = closest
    others = [j for j in range(len(heights)) if j != i]
    den = [mp.mpc(real(gap), real(gamma-w)) for w in heights]
    real_den = [mp.mpc(real(gap), -real(w)) for w in heights]
    d = abs(den[i])
    r = min(real(F(5, 2)), *(abs(den[j]) for j in others))
    rp = (d+r)/2
    if not d < rp < r or not all(abs(v) > rp for v in real_den):
        raise ValueError("No common certified radius")
    c = list(map(real, residues))
    M = sum(abs(c[j])/(abs(den[j])-rp) for j in others)
    M0 = sum(abs(cj)/(abs(v)-rp) for cj, v in zip(c, real_den))

    def triangle(k):
        return sum(abs(c[j]/c[i])*(d/abs(den[j]))**(k+1) for j in others)

    lo, hi = -1, 1
    while triangle(hi) > mp.mpf(".01"):
        hi *= 2
    while hi-lo > 1:
        mid = (lo+hi)//2
        if triangle(mid) > mp.mpf(".01"):
            lo = mid
        else:
            hi = mid
    row.update(d=d, radius=rp, M=M, real_M=M0, first_one_percent_k=hi, samples=[])
    for k in sorted({0,4,16,64,256,max(0,hi-1),hi,hi+1}):
        # Ratios to the leading pole retain small residuals even when 1+residual rounds to 1.
        remainder = sum(c[j]/c[i]*(den[i]/den[j])**(k+1) for j in others)
        real_coeff = sum(c[j]/abs(c[i])*(d/real_den[j])**(k+1) for j in range(len(c)))
        b, bc, b0 = triangle(k), M*d/abs(c[i])*(d/rp)**k, M0*d/abs(c[i])*(d/rp)**k
        combined = abs(1+remainder) + real_coeff.real
        tol = 128*(k+1)*mp.eps
        holds = (abs(remainder) <= b*(1+tol) and abs(remainder) <= bc*(1+tol)
                 and abs(real_coeff) <= b0*(1+tol) and combined+tol >= 1-bc-b0)
        row["samples"].append(dict(k=k, triangle=b, actual_error=abs(remainder), cauchy=bc,
                                   real_actual=abs(real_coeff), real_cauchy=b0,
                                   combined=combined, residual_bounds_hold=holds))
    return row


def resolution():
    pair = [F(9,4), F(-9,4)]
    aligned = pole_probe(pair, [F(1,2)]*2, pair[0])
    v = mp.mpc(real(pair[0]), real(pair[0]))
    cancelled = {}
    for k in (1,5,9,33,65):
        cancelled[str(k)] = abs(2*mp.re((abs(v)/v)**(k+1)))
    limit = 2*real(pair[0])**2*mp.log(100)
    rows = []
    for h in map(F, [1, "1/2", "1/8", "1/32"]):
        w = F(3,2)
        poles = [w, -w, w+h, -(w+h)]
        for frac in map(F,[0, "1/4", "1/2", "3/4"]):
            row = pole_probe(poles, [F(1,2)]*2+[F(-1,2)]*2, w+frac*h)
            row.update(h=str(h), fraction=str(frac))
            if frac == 0:
                row["k_times_h_squared"] = row["first_one_percent_k"]*real(h)**2
                row["ratio_to_limit"] = row["k_times_h_squared"]/limit
            rows.append(row)
    return dict(single_pair_cancelled=cancelled, single_pair_aligned=aligned, limit=limit, pairs=rows)


def positive_mass(U, w):
    V = mp.mpf(3)*U/2
    a = mp.mpf(1)/4
    cuts = [mp.mpf(U)]
    first = int(mp.floor((w*U-mp.pi/2)/mp.pi))+1
    for j in range(first, int(mp.ceil((w*V-mp.pi/2)/mp.pi))):
        cut = (mp.pi/2+j*mp.pi)/w
        if U < cut < V:
            cuts.append(cut)
    cuts.append(V)
    lam = mp.mpc(a, w)
    mass = sum(mp.re((mp.exp(lam*y)-mp.exp(lam*x))/lam)
               for x,y in zip(cuts,cuts[1:]) if mp.cos(w*(x+y)/2)>0)
    quadrature = mp.quad(lambda u: mp.exp(a*u)*max(0, mp.cos(w*u)), cuts)
    return mass, quadrature, len(cuts)-2


def moment(k, w, gamma):
    E = mp.mpf("335.5")
    def term(t):
        den = mp.mpc(mp.mpf("335.25"), gamma-t)
        return (E/den)**k/den
    return (term(w)+term(-w))/2


def moment_integral(k, w, gamma):
    E, rate = mp.mpf("335.5"), mp.mpf("335.25")
    mode, sd = k/rate, mp.sqrt(k+1)/rate
    end = 4*mode
    cuts = sorted({mp.mpf(0),mode,end} | {mode+t*sd for t in (-16,-8,-4,4,8,16) if mode+t*sd>0})
    def integrand(u):
        if u == 0:
            return 0
        return (mp.exp(k*mp.log(E*u)-rate*u-mp.loggamma(k+1))*mp.cos(w*u)
                *mp.exp(-mp.j*gamma*u))
    approx = mp.quad(integrand, cuts)
    truncation = (E/rate)**k/rate * mp.gammainc(k+1,rate*end,mp.inf,regularized=True)
    return dict(k=k, omega=w, gamma=gamma, absolute_discrepancy=abs(approx-moment(k,w,gamma)),
                omitted_envelope=truncation)


def windows():
    E, rate = mp.mpf("335.5"), 334
    rows, negative, independent = [], [], []
    for U in (1,2,4,8):
        k, V = 420*U, mp.mpf("1.5")*U
        scale = (E/rate)**k/rate
        low = scale*mp.gammainc(k+1,0,rate*U,regularized=True)
        high = scale*mp.gammainc(k+1,rate*V,mp.inf,regularized=True)
        for w in (1,7,20):
            I, I_quad, roots = positive_mass(U,w)
            for gamma in (0, w, mp.mpf(w)+mp.mpf(".25")):
                z, z0 = moment(k,w,gamma), moment(k,w,0)
                lhs = abs(z)+z0.real
                rhs = 2*(I+low+high)
                rows.append(dict(U=U,k=k,omega=w,gamma=gamma,roots=roots,mass=I,
                                 mass_quadrature_error=abs(I-I_quad),left_tail=low,right_tail=high,
                                 complex_magnitude=abs(z),real_term=z0.real,lhs=lhs,rhs=rhs,margin=rhs-lhs))
        z0 = -moment(k,0,0).real
        negative.append(dict(U=U,k=k,lhs=abs(z0)+z0,
                             signed_margin=2*(low+high)-(abs(z0)+z0),
                             omit_real_margin=2*(low+high)-abs(z0)))
        if U <= 2:
            independent.append(moment_integral(k,7,7))
    return dict(windows=rows,negative_control=negative,moment_quadrature=independent)


def compare(a,b):
    if isinstance(a,dict):
        if a.keys()!=b.keys():
            raise ValueError("Different output fields at the two precisions")
        return max((compare(a[k],b[k]) for k in a),default=0)
    if isinstance(a,list):
        if len(a)!=len(b):
            raise ValueError("Different output lengths")
        return max((compare(x,y) for x,y in zip(a,b)),default=0)
    if isinstance(a,mp.mpf):
        return abs(a-b)/max(1,abs(a),abs(b))
    if a!=b:
        raise ValueError(f"Discrete classification changed: {a} vs {b}")
    return 0


def serialize(a):
    if isinstance(a,dict):
        return {k:serialize(v) for k,v in a.items()}
    if isinstance(a,list):
        return list(map(serialize,a))
    return mp.nstr(a,20) if isinstance(a,mp.mpf) else a


def run():
    runs = []
    for digits in (70,110):
        with mp.workdps(digits):
            runs.append(dict(resolution=resolution(), **windows()))
    with mp.workdps(110):
        delta = compare(*runs)
        return serialize(dict(**runs[1], precision_digits=[70,110], cross_precision_max=delta))
