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
