import sys,re
def show(mod,name):
    src=open('CflibsFormal/'+mod).read().split('\n')
    for i,l in enumerate(src):
        if re.match(r'^(@\[[^\]]*\]\s*)?(private |protected )?(theorem|lemma) '+re.escape(name)+r'(\s|$)',l):
            # docstring: walk back
            j=i-1
            while j>=0 and not src[j].lstrip().startswith('/--'): j-=1
            doc='\n'.join(src[j:i])
            k=i; stmt=[]
            while k<len(src):
                stmt.append(src[k])
                if ':=' in src[k]: break
                k+=1
            print(f'==== {mod}:{i+1} {name}'); print(doc); print('\n'.join(stmt)); print()
            return
    print('NOTFOUND',mod,name)
for a in sys.argv[1:]:
    m,n=a.split('::'); show(m,n)
