Source Code for experiments in ECAI Paper #1386

Contains the situated object dataset, preprocessed to merge coexisting quality values for the same quality into one (e.g., physical_hard and physical_brittle become physical_hard_brittle).

It is possible to induce theories from scratch with HeRO by running training_linprio.py. These are taken to be theories with "arbitrary" priority relation. Because this is code from a previous experiment we have done, it actually induces theories for all qualities in the situated object dataset and will take some time.

It is possible to induce theories from scratch that use specificity based priority relations, for the temperature quality, by running training_specprio.py.

To test instructability, run either testInstructability_linprio.py or testInstructability_specprio.py. These will produce logs of the generated samples of instruction protocols as described in the paper. These scripts assume some theories are already present in the folders theories_linprio and theories_specprio respectively.

To change the quality for which to induce theories with specificity-based priority:
1. delete all theories from theories_specprio.
2. Set the prefix variable in training_specprio.py to the desired prefix. Available prefixes are '' (empty string) for object type, 'cleanliness', 'color', 'dampness', 'dimension', 'fullness', 'material', 'physical', 'place', 'price', 'room', 'shape', 'size', 'temperature', 'transparency', 'weight'
3. Set the prefix variable in testInstructability_specprio.py to the same value.
4. Run training_specprio.py then testInstructability_specprio.py.