import CflibsFormal
open CflibsFormal
set_option pp.fullNames true

#check @CflibsFormal.dampedMap
#print CflibsFormal.dampedMap
#check @CflibsFormal.dampedMap_lipschitz
#check @CflibsFormal.dampedMap_contracts
#check @CflibsFormal.tDamped_mobius_converges
#check @CflibsFormal.exists_weights_iff

#print axioms CflibsFormal.dampedMap_lipschitz
#print axioms CflibsFormal.dampedMap_contracts
#print axioms CflibsFormal.tDamped_mobius_converges
#print axioms CflibsFormal.exists_weights_iff
