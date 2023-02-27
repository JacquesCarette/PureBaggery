# Things that need done 

Vaguely in order

- pull out stdlib-related Monoid kit from current files
- pull out prop-eq based Monoid kit from current files
- pull out Monoid Hom stuff too
- implement a different ~~ on SillyList that is the more obvious
  "term model" induced by the exact requirements
- pull out a "free monoid" signature
- show that anything with that signature is a free monoid
- pull out a "free commutative monoid" signature
- experiment with making SillyList abstract
- implement bag over PermJ
- show that the various ~~ are appropriately equivalent
- show that the various Free X are equivalent (as categories of X)
- implement "Cycle n"
- show the Action Groupoid of each of the above [make into sub-tasks]
- derive a Position type from each of the above
- implement derivative (and show how it corresponds to an action on Position)
- show what the orbits are

# Things that are done

- List implemented as a quotiented term algebra, with the quotienting
  relation having (congruence, symmetry, reflexive) provable
- Strict Free Monoid as lists over propositional sets.
- Bags as quotiented term algebra with the quotienting 
  relation having (congruence, symmetry, reflexive) provable
