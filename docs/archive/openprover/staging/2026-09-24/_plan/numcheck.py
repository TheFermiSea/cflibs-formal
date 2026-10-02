import math, random
random.seed(1)
SA=lambda t: 1.0 if t==0 else (1-math.exp(-t))/t
worst=0
for _ in range(200000):
    a=random.choice([random.random()*0.01, random.random()*5, random.random()*60]); b=random.choice([random.random()*0.01, random.random()*5, random.random()*60])
    if a==b: continue
    r=abs(math.log(SA(a))-math.log(SA(b)))/(abs(a-b)/2); worst=max(worst,r)
print('FT13b max ratio (<=1 expected):', worst)
# FT15 lipschitz max
worst=0
for _ in range(20000):
    n=random.randint(1,6); g=[random.uniform(0.1,5) for _ in range(n)]; E=[random.uniform(0,10) for _ in range(n)]
    kB=random.uniform(0.5,2); T1=random.uniform(0.5,20); T2=random.uniform(0.5,20)
    U=lambda T: sum(gi*math.exp(-Ei/(kB*T)) for gi,Ei in zip(g,E))
    mE=lambda T: sum(gi*Ei*math.exp(-Ei/(kB*T)) for gi,Ei in zip(g,E))/U(T)
    lhs=abs(math.log(U(T1))-math.log(U(T2))); rhs=mE(max(T1,T2))*abs(1/(kB*T1)-1/(kB*T2))
    if rhs>0: worst=max(worst,lhs/rhs)
print('FT15 lip max ratio (<=1):', worst)
# FT15 monotone
bad=0
for _ in range(20000):
    n=random.randint(1,6); g=[random.uniform(0.1,5) for _ in range(n)]; E=[random.uniform(-5,10) for _ in range(n)]
    kB=1; T1,T2=sorted([random.uniform(0.5,20),random.uniform(0.5,20)])
    U=lambda T: sum(gi*math.exp(-Ei/(kB*T)) for gi,Ei in zip(g,E))
    mE=lambda T: sum(gi*Ei*math.exp(-Ei/(kB*T)) for gi,Ei in zip(g,E))/U(T)
    if mE(T1)>mE(T2)+1e-9: bad+=1
print('FT15 monotone violations:', bad)
# FT05 cut ratio strict mono
bad=0
for _ in range(20000):
    n=random.randint(2,6); g=[random.uniform(0.1,5) for _ in range(n)]; E=[random.uniform(0,10) for _ in range(n)]
    cut=random.uniform(0,10)
    if not(any(e<cut for e in E) and any(e>=cut for e in E)): continue
    T1,T2=sorted([random.uniform(0.3,20),random.uniform(0.3,20)])
    if T2-T1<1e-3: continue
    R=lambda T: sum(gi*math.exp(-Ei/T) for gi,Ei in zip(g,E))/sum(gi*math.exp(-Ei/T) for gi,Ei in zip(g,E) if Ei<cut)
    if not R(T1)<R(T2): bad+=1
print('FT05 violations:', bad)
# FT01 mobius
bad=0
for _ in range(5000):
    g=random.uniform(0.01,0.99); c=random.uniform(0.01,5); lam=random.uniform(0.01,1); T=random.uniform(0.001,100)
    for _ in range(20000): T=(1-lam)*T+lam*T/(g+c*T)
    if abs(T-(1-g)/c)>1e-6*(1+(1-g)/c) and (1-lam+lam*g)**20000>1e-8: pass
    elif abs(T-(1-g)/c)>1e-6*(1+(1-g)/c): bad+=1; print('mob',g,c,lam,T,(1-g)/c)
print('FT01 mobius nonconverged (slow cases possible):', bad)
# FT17 Newton
bad=0
for _ in range(3000):
    n=random.randint(1,4); S=[10**random.uniform(-3,3) for _ in range(n)]; Nt=[10**random.uniform(-3,3) for _ in range(n)]
    G=lambda x: sum(a*s/(x+s) for a,s in zip(Nt,S))
    lo,hi=0,sum(Nt)+1
    for _ in range(200):
        m=(lo+hi)/2
        if m<G(m): lo=m
        else: hi=m
    r=(lo+hi)/2
    Nw=lambda x: x-(x-G(x))/(1+sum(a*s/(x+s)**2 for a,s in zip(Nt,S)))
    x=random.choice([0, random.uniform(0,10*r+1), 1e6])
    x1=Nw(x)
    if x1>r*(1+1e-9)+1e-12 or r>G(x1)*(1+1e-9)+1e-12: bad+=1
    for _ in range(200): x=Nw(x)
    if abs(x-r)>1e-7*(1+r): bad+=1
print('FT17 violations:', bad)
# FT02 sensitivity
bad=0
for _ in range(20000):
    b=random.uniform(0,0.5); a1=random.uniform(0.01,10); a2=a1*random.uniform(1,10)
    def root(a):
        l=math.log(a)
        for _ in range(500): l=math.log(a)+b*math.exp(l/2)
        return l
    try:
        l1,l2=root(a1),root(a2)
    except OverflowError:
        continue
    if not all(map(math.isfinite,[l1,l2])): continue
    if abs(math.log(a1)+b*math.exp(l1/2)-l1)>1e-9 or abs(math.log(a2)+b*math.exp(l2/2)-l2)>1e-9: continue
    q=b*math.exp(max(l1,l2)/2)/2
    if q>=1: continue
    d=math.log(a2)-math.log(a1)
    if not (d<=l2-l1+1e-12 and l2-l1<=d/(1-q)+1e-9): bad+=1
print('FT02 sens violations:', bad)
