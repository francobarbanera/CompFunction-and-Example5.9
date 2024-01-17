The Haskell module DataType implements Processes, Global Types and Compliance derivations as defined in
F.Barbanera, M.Dezani-Ciancaglini  Partial Typing for Open Compliance in Multiparty Sessions

The module CompositionFunction implements the function g with
Input: d (compliance derivation ), 
       gt1, gt2, gt3 (global types),
       ph, pv, pw (participants names).
Output: the global type for the composition via gateways (built out of d) of any three sessions typable, 
        respectively, with gt1, gt2 and gt3, where ph, pv, pw are the name of the participants for the processes in d.
The function g is the one defined in the proof of Theorem 5.8 of the above mentioned paper
where the participant names have been left implicit for readability.
The output of g can be an infinite global type, any approximation of which can be displayed by means of the function prune
also implemented in this module. prune essentially "cuts" a given global type at a given level.

The module Example5dot9 implements the objects present in Example 5.9 of the above mentioned paper.

