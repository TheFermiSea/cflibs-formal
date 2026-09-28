import CflibsFormal
set_option pp.funBinderTypes true
open CflibsFormal

-- Card evidence for ft14i.kirchhoff-source-planck: re-derive the printed statement and confirm
-- the axiom set independently of docs/catalog.jsonl. Not library code.
#check @CflibsFormal.source_eq_planck
#print CflibsFormal.lineOpacity
#print CflibsFormal.lineEmissivity
#print axioms CflibsFormal.source_eq_planck
