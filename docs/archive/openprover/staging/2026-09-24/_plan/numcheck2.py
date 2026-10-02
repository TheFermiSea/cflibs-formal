import random
random.seed(2)
bad=0
for _ in range(3000):
    n=random.randint(2,8); G=random.randint(1,3)
    grp=[random.randrange(G) for _ in range(n)]; w=[random.uniform(0.1,3) for _ in range(n)]
    x=[random.uniform(-3,3) for _ in range(n)]; y=[random.uniform(-3,3) for _ in range(n)]
    def gm(f,e):
        num=sum(w[k]*f[k] for k in range(n) if grp[k]==e); den=sum(w[k] for k in range(n) if grp[k]==e)
        return num/den if den!=0 else 0.0
    wc=lambda f,h: sum(w[k]*(f[k]-gm(f,grp[k]))*(h[k]-gm(h,grp[k])) for k in range(n))
    SS=wc(x,x)
    if SS<1e-6: continue
    b=wc(x,y)/SS
    rss_opt=sum(w[k]*(y[k]-(gm(y,grp[k])-b*gm(x,grp[k]))-b*x[k])**2 for k in range(n))
    for _ in range(20):
        a=[random.uniform(-5,5) for _ in range(G)]; beta=random.uniform(-5,5)
        if rss_opt>sum(w[k]*(y[k]-a[grp[k]]-beta*x[k])**2 for k in range(n))+1e-9: bad+=1
print('FT04 isMin violations', bad)
bad=0
for _ in range(3000):
    na=random.randint(1,5); nb=random.randint(1,5)
    Ea=[random.uniform(0,5) for _ in range(na)]; Eb=[random.uniform(0,5) for _ in range(nb)]
    ma=sum(Ea)/na; mb=sum(Eb)/nb
    SS=sum((e-ma)**2 for e in Ea)+sum((e-mb)**2 for e in Eb)
    if SS<1e-6: continue
    wa=[1/na-(ma-mb)*(e-ma)/SS for e in Ea]; wb=[-1/nb-(ma-mb)*(e-mb)/SS for e in Eb]
    lhs=sum(v*v for v in wa)+sum(v*v for v in wb); rhs=1/na+1/nb+(ma-mb)**2/SS
    if abs(lhs-rhs)>1e-9*(1+rhs): bad+=1
print('FT10 interceptDiff violations', bad)
