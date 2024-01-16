The Haskell code implements the function g with
Input: d (compliance derivation ), 
       g1, g2, g3 (global types),
       ph, pv, pw (participants names).
Output: the global type for the composition via gateways (built out of d) of any three sessions typable, 
        respectively, with g1, g2 and g3, where ph, pv, pw are the name of the participants for the processes in d.
The function g is the one defined in the proof of Theorem 5.8 of
F.Barbanera, M.Dezani-Ciancaglini  Partial Typing for Open Compliance in Multiparty Sessions
where the participant names have been left implicit.
The output of g can be an infinite global type, any approximation of which can be displayed by means of the function prune
that takes a number n and a global type and returns the global type with all branches cut after n interactions.
In the code are defined also the global types used in Example 5.9.
