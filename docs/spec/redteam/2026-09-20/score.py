import json, re, sys, pathlib, collections
S = pathlib.Path(sys.argv[1]); run = sys.argv[2]
labels = json.load(open(S/'labels.json')); res = json.load(open(S/f'results_{run}.json'))
rows=[]; ok_pass=0; ok_class=0; n_f=0; n_d=0
for vid, meta in sorted(labels.items()):
    r = res.get(vid, {}); v = r.get('verdict'); c = r.get('drift_class')
    faithful = meta['drift_class']=='none'
    if faithful:
        n_f+=1; hit = (v=='passed'); ok_pass += hit
    else:
        n_d+=1; hit = (v=='gaps_found') and (c==meta['drift_class']); ok_class += hit
    rows.append((vid, meta['variant'], meta['drift_class'], v, c, 'OK' if hit else 'MISS'))
print(f"run={run}  faithful accepted {ok_pass}/{n_f}   drift flagged with correct class {ok_class}/{n_d}")
for r in rows: print('  '.join(str(x) for x in r))

# run 3 (two-class artifact): strict hit iff verdict gaps_found and reported edit_class == label edit_class
# and reported mechanism_class in {label mechanism_class, label edit_class}; faithful iff passed.
if run.startswith('run3'):
    ok=0; nd=0; okf=0; nf=0; loose=0
    for vid, meta in sorted(labels.items()):
        r=res.get(vid,{}); v=r.get('verdict'); e=r.get('edit_class'); m=r.get('mechanism_class')
        faithful=meta['drift_class']=='none'
        if faithful:
            nf+=1; okf+=(v=='passed'); continue
        nd+=1
        strict=(v=='gaps_found') and e==meta['edit_class'] and m in (meta['mechanism_class'], meta['edit_class'])
        lo=(v=='gaps_found') and ({e,m} & {meta['edit_class'], meta['mechanism_class']})
        ok+=bool(strict); loose+=bool(lo)
        print(f"  {vid} {meta['variant']} edit={meta['edit_class']} mech={meta['mechanism_class']} | got {v} edit={e} mech={m} | {'OK' if strict else 'MISS'}")
    print(f"run={run} faithful {okf}/{nf}  drift strict(two-class) {ok}/{nd}  drift loose(any-match) {loose}/{nd}")
