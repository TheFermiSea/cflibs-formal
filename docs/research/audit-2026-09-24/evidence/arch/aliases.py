import re,glob,sys
# Find public theorems whose proof is a bare term application of one other named theorem (pure alias/restatement)
res=[]
for f in sorted(glob.glob('CflibsFormal/**/*.lean',recursive=True)):
    src=open(f).read()
    # split into declarations at lines starting with theorem/lemma
    decl_re=re.compile(r'^(?:@\[[^\]]*\]\s*)?(theorem|lemma)\s+(\S+)(.*?)(?=^(?:/--|/-!|@\[|theorem |lemma |private |noncomputable |def |end |section|namespace|open |variable|example|instance|abbrev|structure|--)|\Z)',re.S|re.M)
    for m in decl_re.finditer(src):
        name=m.group(2); body=m.group(3)
        # find top-level ':=' that ends the statement: take last ':=' occurrence not followed by 'by'
        idx=body.find(':=\n')
        if idx<0:
            idx=body.find(':= ')
        if idx<0: continue
        proof=body[idx+2:].strip()
        if proof.startswith('by'):
            p2=proof[2:].strip()
            if re.fullmatch(r'exact\s+[A-Za-z_][\w.\'₀-₉]*(\s+[^\n]*)?',p2) and '\n' not in p2:
                res.append((f,name,'by exact '+p2[6:60]))
            continue
        if re.match(r'^[A-Za-z_⟨(][^\n]*$',proof) or len(proof.splitlines())<=3:
            head=re.match(r'[\w.\'⟨(]+',proof)
            res.append((f,name,proof.replace('\n',' ')[:80]))
print(len(res))
for r in res: print(*r,sep=' | ')
