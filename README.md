----------------------------------------
The code in this repository is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published
by the Free Software Foundation, either version 3 of the License,
or (at your option) any later version.

It is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.
For a copy of the GNU General Public License see <http://www.gnu.org/licenses/>.

--------------------------------------------


The file "The Function Implemented By The Program FunctionDefinition.hs.pdf contains" an excerpt of the proof of Theorem 5.8. In it only the definition 
of the function G is present.

The module FunctionDefinition.hs contains the Haskell implementation (as function "g") of the function defined in the above pdf file.  
The function g has
Input: d (compliance derivation), gt1, gt2, gt3 (global types), ph, pv, pw (participants names). 
Output: the global type for the composition via gateways (built out of d) of any three sessions typable, respectively, with gt1, gt2 and gt3, where ph, pv, pw are the names of the participants for the processes in d. 
The participant names do not occur as arguments of the function G  for readability.
The output of g can be an infinite global type, any approximation of which can be displayed by means of the function prunegt also implemented in this module. prunegt essentially "cuts" a given global type at a given level. 

The module DataTypes.hs contains the Haskell datatype definitions for Processes, Global Types and Compliance derivations. 

The module Example5dot9 implements the objects present in Example 5.9.

The module ExampleSect6 implements the objects present in Section 6.

