The module FunctionDefinitions implements the function g with 
Input: d (compliance derivation), gt1, gt2, gt3 (global types), ph, pv, pw (participants names). 
Output: the global type for the composition via gateways (built out of d) of any three sessions typable, respectively, with gt1, gt2 and gt3, where ph, pv, pw are the name of the participants for the processes in d. 
The function g is the one defined in the proof of Theorem 5.8 of the above mentioned paper, where the participant names have been left implicit for readability. 
The output of g can be an infinite global type, any approximation of which can be displayed by means of the function prunegt also implemented in this module. prunegt essentially "cuts" a given global type at a given level. 
This module also implements the function gateway (implicitely defined in Fig.5) with 
Input: d (compliance derivation), ph, pv, pw (participants names). 
Output: the gateways induced by the derivation d for the given participant names. 
The gateways can be infinite processes, any approximation of which can be displayed by means of the function prunproc.

The module Example5dot9 implements the objects present in Example 5.9 of the above mentioned paper.

The module ExampleSect6 implements the objects present in Section 6 of the above mentioned paper.

