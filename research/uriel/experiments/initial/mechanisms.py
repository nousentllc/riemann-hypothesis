"""Finite mechanism experiments. These functions do not prove Lean theorems."""
from fractions import Fraction as F
from itertools import combinations
import cmath
import math
import random

import numpy as np
from scipy.integrate import quad
from scipy.special import logsumexp
from scipy.stats import gamma


def log_exp_integral(rate, lo, hi):
    """Log integral of exp(rate*u), with empty intervals represented by -inf."""
    if hi <= lo:
        return -math.inf
    if rate == 0:
        return math.log(hi - lo)
    if rate < 0:
        return rate * lo + math.log(-math.expm1(rate * (hi-lo))) - math.log(-rate)
    return rate * hi + math.log(-math.expm1(-rate * (hi-lo))) - math.log(rate)


def analytic():
    theta, beta, delta, eta = .5, .75, .5, .05
    windows = []
    for u in [1, 4, 16, 64, 256]:
        log_mass = log_exp_integral(beta-theta, u, (1+delta)*u)
        delayed = log_exp_integral(beta-theta, max(u, 50), (1+delta)*u)
        windows.append(dict(U=u, positive_log_ratio=log_mass-eta*u,
                            negative_mass=0, negative_residue=-1,
                            delayed_log_ratio=None if delayed == -math.inf else delayed-eta*u))
    tails = []
    for delta in [.25, .5, 1.]:
        ell = 2 + 6/delta
        sigma = ell*(1+delta)*(2+ell)
        constant = math.e/(sigma-2-ell) + 1/(sigma-2+ell)
        for u in [1, 4, 16]:
            k = math.ceil((1+delta/2)*sigma*u)
            rate = sigma-2
            log_probability = float(logsumexp([gamma.logcdf(u, k+1, scale=1/rate),
                                              gamma.logsf((1+delta)*u, k+1, scale=1/rate)]))
            scaled_tail = log_probability - (k+1)*math.log(rate) + k*math.log(sigma)
            log_chernoff = float(logsumexp([
                -ell*(1+delta)*u-(k+1)*math.log(rate-ell),
                ell*u-(k+1)*math.log(rate+ell)])) + k*math.log(sigma)
            mass = gamma.cdf((1+delta)*u,k+1,scale=1/sigma)-gamma.cdf(u,k+1,scale=1/sigma)
            tails.append(dict(delta=delta,U=u,sigma=sigma,k=k,kernel_window_mass=float(mass),
                              log_scaled_tail=scaled_tail,log_scaled_chernoff=log_chernoff,
                              log_source_C=math.log(constant),
                              passes=scaled_tail <= log_chernoff+1e-9 and log_chernoff <= math.log(constant)+1e-9))
    low_sigma=[]
    for u in [1,4,16,64,256]:
        k=math.ceil(3.75*u)
        logp=float(logsumexp([gamma.logcdf(u,k+1),gamma.logsf(1.5*u,k+1)]))
        low_sigma.append(dict(U=u,k=k,log_scaled_tail=logp+k*math.log(3)))
    quadrature=[]
    # g(u)=sign*exp(beta*u)*cos(omega*u); split into two complex poles.
    for sign in [-1,1]:
        for omega in [0.,1.2]:
            for k in [0,4,16]:
                for t in [0.,.7]:
                    s=3+1j*t
                    exact=sign/2*((s-beta-1j*omega)**(-k-1)+(s-beta+1j*omega)**(-k-1))
                    scale=abs(exact)
                    def integrand(u):
                        if u==0 and k:
                            return 0j
                        logw=(k*math.log(u) if k else 0)-(3-beta)*u-math.lgamma(k+1)
                        return sign*math.exp(logw)/scale*math.cos(omega*u)*cmath.exp(-1j*t*u)
                    re,er=quad(lambda u:integrand(u).real,0,np.inf,epsabs=1e-11,epsrel=1e-11,limit=250)
                    im,ei=quad(lambda u:integrand(u).imag,0,np.inf,epsabs=1e-11,epsrel=1e-11,limit=250)
                    relative=abs(complex(re,im)-exact/scale)
                    quadrature.append(dict(sign=sign,omega=omega,k=k,t=t,relative_error=relative,
                                           estimated_scaled_error=er+ei))
    growth=[]
    for u in [1,4,16,64,256]:
        k=math.ceil(3.75*u)
        for d in [2.25,2.4]:
            r,e=2.4,2.5
            loss=.5*math.log(r/d)
            logratio=-k*math.log(d)-float(logsumexp([-k*math.log(r),loss*u-k*math.log(e)]))
            growth.append(dict(U=u,k=k,d=d,eta=loss,log_pole_to_allowance=logratio))
    # Weighted spike is exactly height on [10.4,10.6], zero at integer mesh points.
    return dict(windows=windows,tails=tails,low_sigma=low_sigma,quadrature=quadrature,growth=growth,
                spike=dict(U=10,V=15,mesh_step=1,sampled_mass=0,full_weighted_mass=20,
                           allowed_mass=math.exp(.05*10),missed_by_mesh=True))


def budget_terms(p):
    """Logs of normalized bracket; all parameters except eps/logx are logs."""
    z,e=p['logx'],p['eps']
    return [math.log(2)+p['ab']-p['m']-p['d2']+float(np.logaddexp(0,2*p['m']-p['k'])),
            math.log(4)+p['m']+e*z-p['dT']-p['d2'],
            math.log(2)+p['k']+2*e*z-p['dT']-2*p['n']]


def budget_constraints(p):
    z,e=p['logx'],p['eps']
    return dict(x=z>=math.log(3),eps=e>0,weight=p['ab']<=math.log(2)+z+1e-9,
                density_T=p['dT']>=-math.log(2)-e*z/8-1e-9,
                density_2=p['d2']>=-e*z-1e-9 and p['d2']<=1e-9,
                densities_at_most_one=p['dT']<=1e-9,
                m_lower=p['m']>=(.5-e)*z-1e-9,m_upper=p['m']<=(.5+e/2)*z+1e-9,
                k_lower=p['k']>=z+p['m']-1e-9,
                k_upper=p['k']<=2*p['n']+(.5-e)*z+1e-9,
                absorb_constant=math.log(26)<=3*e*z/8+1e-9)


def budget_row(p,label):
    terms=budget_terms(p)
    z,e=p['logx'],p['eps']
    # From Q*d2/2*(G-4*x^(.5+eps)) <= x^(C*eps)*B + 2Q/x.
    logupper=float(logsumexp([5*e*z+float(logsumexp(terms)),
                              math.log(4)-z-p['d2'],math.log(4)+(.5+e)*z]))
    target=(.5+8*e)*z
    c=budget_constraints(p)
    return dict(label=label,parameters=p,constraints=c,admissible=all(c.values()),
                term_log_values=terms,bracket_log_exponent=float(logsumexp(terms))/z,
                log_upper_to_target=logupper-target,bound_passes=logupper<=target+1e-9)


def arithmetic():
    rng=random.Random(20261122)
    selected=[]
    for e in [.01,.03,.1]:
        for z in [10.,100.,1000.]:
            p=dict(eps=e,logx=z,ab=z,m=(.5-e/16)*z,n=(2+8*e)*z,
                   k=(4.5+10*e)*z,dT=-e*z/8,d2=-e*z)
            selected.append(budget_row(p,'selected_scale'))
    sampled=[]
    for e in [.01,.03,.1]:
        z=1000.
        for _ in range(300):
            m=rng.uniform((.5-e)*z,(.5+e/2)*z)
            n=(2+8*e)*z
            p=dict(eps=e,logx=z,ab=z,m=m,n=n,k=rng.uniform(z+m,2*n+(.5-e)*z),
                   dT=rng.uniform(-math.log(2)-e*z/8,0),d2=rng.uniform(-e*z,0))
            sampled.append(budget_row(p,'sample'))
    base=dict(selected[5]['parameters'])
    ablations=[]
    for label,key,shift in [('thin_T','dT',-base['logx']),('thin_2','d2',-base['logx']),
                            ('rank_high','k',base['logx']),('group_small','n',-base['logx'])]:
        p=dict(base);p[key]+=shift;ablations.append(budget_row(p,label))
    p=dict(base);p['k']=0.;ablations.append(budget_row(p,'rank_low'))
    residuals=[]
    for _ in range(200):
        n=rng.randint(2,200);nt=rng.randint(1,n);n2=rng.randint(1,n)
        m=rng.randint(1,50);k=rng.randint(1,1000);x=rng.randint(3,100)
        b=rng.uniform(.2,2);a=rng.uniform(.1,10);e=rng.uniform(.01,.1)
        bracket=nt*a*(1+m*m/k)+m*(2*n*m*b*x**e+n2*k*b*x**e/(n*(n*x**(-e))))
        normalized=bracket/(nt*m*b*(n2/n)/2)
        independent=2*a/(m*b*(n2/n))*(1+m*m/k)+4*m*x**e/((nt/n)*(n2/n))+2*k*x**(2*e)/((nt/n)*n*n)
        residuals.append(abs(normalized-independent)/abs(normalized))
    x=100000;lhs=x**10;rhs=x**5*(x+3)
    amplification=[]
    for x in [10,100,1000,100000]:
        # Source weak model etaBar=1,eBar=0,b=1,nT=1,a=x,eps=K=1,cHH=10.
        amplification.append(dict(x=x,weak_component_bounds=True,strong_budget_ratio=x**8,
                                  required_etaBar=x**-8))
    return dict(selected=selected,sampled=sampled,ablations=ablations,
                identity_cases=200,identity_max_relative_error=max(residuals),
                weak_counterexample=dict(x=100000,lhs=str(lhs),rhs=str(rhs),ratio=lhs/rhs,
                                         inequality=lhs>rhs),amplification=amplification)


def select_window(R,B,U,T):
    """Exact-rational port of window1; inputs may represent logarithmic indices."""
    T=set(map(F,T));B=F(B);U=F(U)
    if R<0 or len(T)>R or B<1 or U<=0:
        raise ValueError('window1 preconditions violated')
    if not R:
        return U/2
    candidates=sorted(a for a in T if U/(2*B)<a<=U)
    if candidates:
        a=candidates[0]
        return select_window(R-1,B,U/(2*B),T-{a})
    return U/2


def whole_window(B,y,T):
    """Independent continuum oracle: no [a,B*a) intersects closed [y,2y]."""
    return all(not(a<=2*y and max(y,a)<B*a) for a in T)


def cohomology():
    cases=0;bad=[];ratios=[]
    for B in map(F,[1,2,4]):
        U=F(64);cut=U/(2*B)
        grid=sorted({F(-1),F(0),cut-F(1,100),cut,cut+F(1,100),U/2,U,U+1,F(100)})
        for size in range(5):
            for T in combinations(grid,size):
                y=select_window(4,B,U,T);lower=U/(2**6*B**4)
                ok=lower<=y and 2*y<=U and whole_window(B,y,T)
                cases+=1;ratios.append(float(y/lower))
                if not ok:bad.append(dict(B=str(B),T=list(map(str,T)),y=str(y)))
    rng=random.Random(20261123)
    for _ in range(300):
        R=rng.randint(0,8);B=F(rng.randint(1,16),rng.randint(1,1));U=F(rng.randint(1,1000))
        T={F(rng.randint(-100,2000),rng.randint(1,20)) for _ in range(R)}
        y=select_window(R,B,U,T);lower=U/(2**(R+2)*B**R)
        ok=lower<=y and 2*y<=U and whole_window(B,y,T)
        cases+=1;ratios.append(float(y/lower))
        if not ok:bad.append(dict(B=str(B),T=list(map(str,T)),y=str(y)))
    # Naive y=U/2 fails because a=3U/8 lies below y but B*a lies above y.
    adversarial=[]
    for U in map(F,[64,128,1024]):
        T={3*U/8};y=select_window(1,F(2),U,T)
        adversarial.append(dict(U=str(U),exception=str(next(iter(T))),selected_y=str(y),
                                naive_passes=whole_window(F(2),U/2,T),
                                selected_passes=whole_window(F(2),y,T)))
    rejected=False
    try:select_window(0,2,64,{24})
    except ValueError:rejected=True
    # At u=a=64 the implication is active: the right endpoint is not excluded.
    return dict(cases=cases,failures=bad,min_y_to_lower=min(ratios),max_y_to_lower=max(ratios),
                moving=adversarial,understated_cap_rejected=rejected,
                omitted_exception_passes=whole_window(F(2),F(32),{F(24)}),
                endpoint_failure_detected=not whole_window(F(2),F(32),{F(64)}))


def numeric_constraints(dg,db,mu,mug,m,lg,delta,Q):
    return dict(total_positive=dg+db>0,good_nonnegative=dg>=0,bad_nonnegative=db>=0,
                cut=(dg+db)*mu<=dg*mug+db*(m+lg),delta_nonnegative=delta>=0,
                delta_upper=delta<=F(1,12),rank=db<=3*delta*(dg+db),
                maximum=m<=Q,lower_total=-Q<=mu,denominator=0<=lg<=Q)


def covolume():
    rng=random.Random(20261124);failures=[];slacks=[]
    for _ in range(500):
        dg=F(rng.randint(3,100));db=F(rng.randint(0,int(dg)//3))
        delta=db/(3*(dg+db));Q=F(rng.randint(1,20))
        mu=F(rng.randint(-10,10),10)*Q;m=F(rng.randint(-10,10),10)*Q
        lg=F(rng.randint(0,10),10)*Q
        mug=((dg+db)*mu-db*(m+lg))/dg+F(rng.randint(0,10),10)
        args=(dg,db,mu,mug,m,lg,delta,Q)
        constraints=numeric_constraints(*args)
        slack=mug-(mu-12*delta*Q);slacks.append(float(slack))
        if not all(constraints.values()) or slack<0:failures.append(list(map(str,args)))
    ablations=[]
    for label,dg,db,mu,m,lg in [('rank',2,2,-1,1,1),('maximum',3,1,-1,4,1),
                               ('lower_total',3,1,-4,1,1),('denominator',3,1,-1,1,4)]:
        dg,db,mu,m,lg=map(F,[dg,db,mu,m,lg]);delta=F(1,12);Q=F(1)
        mug=((dg+db)*mu-db*(m+lg))/dg
        c=numeric_constraints(dg,db,mu,mug,m,lg,delta,Q)
        ablations.append(dict(label=label,failed_hypotheses=[k for k,v in c.items() if not v],
                              mu=str(mu),mug=str(mug),target=str(mu-12*delta*Q),
                              conclusion_holds=mug>=mu-12*delta*Q))
    lattices=[]
    for q in [1,2,10,100]:
        v=np.array([1.,q]);g=1+q*q;P=np.outer(v,v)/g
        retained_covol=math.sqrt(float(v@v));image_covol=1/retained_covol
        mug=-2*math.log(retained_covol);lg=2*math.log(g)
        for shear in [0,3,20]:
            L=np.array([[1.,shear],[0.,1.]])
            integral=np.linalg.inv(L)@(g*P)@L
            lattices.append(dict(q=q,shear=shear,denominator=g,
                original_covolume=abs(float(np.linalg.det(L))),retained_intersection_covolume=retained_covol,
                projected_image_covolume=image_covol,good_slope=mug,cut_rhs=mug+lg,
                cut_without_denominator_rhs=mug,idempotence_error=float(np.max(abs(P@P-P))),
                orthogonality_error=float(np.max(abs(P.T-P))),
                integrality_error=float(np.max(abs(integral-np.round(integral))))))
    P=np.array([[1.,2.],[0.,0.]]);v=np.array([0.,1.]);pv=P@v;rest=v-pv
    absorption=[]
    for ez in [.1,1.]:
        for z in [1.,10.,100.,1000.,10000.]:
            t=ez*z/7
            # fixed polynomial envelope; avoid evaluating exp(exp(...)).
            logpoly=float(logsumexp([2*z,2*z,math.log(3)]))
            logloss=math.log(12)-math.exp(t)+logpoly if t<700 else None
            absorption.append(dict(ez=ez,logx=z,log_loss_over_E=logloss,
                                    underflow_safe_pass=t>=700 or logloss<=0))
    return dict(numeric_cases=500,numeric_failures=failures,min_numeric_slack=min(slacks),
                ablations=ablations,lattices=lattices,
                nonorthogonal=dict(idempotence_error=float(np.max(abs(P@P-P))),
                    pythagorean_residual=float(v@v-pv@pv-rest@rest)),
                absorption=absorption,x_dependent_envelope='Q/E=exp(2*x^(ez/7)) gives loss/E=12*exp(x^(ez/7)) > 1')
