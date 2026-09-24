"""Pipeline's own C1/C2 predicates on POOLED lines vs the rank of the design the pipeline
actually fits ([x* | element dummies], plus the common ln n_e column for the joint fit)."""
import warnings; warnings.filterwarnings("ignore")
import numpy as np
from cflibs.inversion.physics.certificates import energy_spread_certificate, joint_rank_certificate

def dummy_rank(rows, with_ne):
    els = sorted({r[0] for r in rows}); idx = {e: i for i, e in enumerate(els)}
    A = []
    for el, z, E, ip in rows:
        x = E + (ip if z == 2 else 0.0)
        row = [x] + [1.0 if idx[el] == j else 0.0 for j in range(len(els))]
        if with_ne: row.append(1.0 if z == 2 else 0.0)   # coefficient on -ln n_e (common to all ions)
        A.append(row)
    A = np.array(A); return np.linalg.matrix_rank(A), A.shape[1]

# Case 1 (C2): every element observed in ONE stage only -> no inter-stage offset -> n_e not identifiable
rows = [("Al", 1, 3.14, 5.99), ("Al", 1, 3.60, 5.99), ("Ti", 2, 3.0, 6.83), ("Ti", 2, 4.0, 6.83), ("Ti", 2, 5.0, 6.83)]
E = [r[2] for r in rows]; s = [1.0 if r[1] == 2 else 0.0 for r in rows]
c2 = joint_rank_certificate(E, s)
print("case1 C2 pooled:", c2.passed if hasattr(c2,'passed') else c2, "| dummy design rank (x,dummies,ne):", dummy_rank(rows, True))
# Case 2 (C1): each element's lines share one upper level (Al I 394.40/396.15 both 3.1427 eV)
rows2 = [("Al", 1, 3.1427, 5.99), ("Al", 1, 3.1427, 5.99), ("Cu", 1, 3.82, 7.73), ("Cu", 1, 3.82, 7.73)]
c1 = energy_spread_certificate([r[2] for r in rows2])
print("case2 C1 pooled:", c1, "| dummy design rank (x,dummies):", dummy_rank(rows2, False))
